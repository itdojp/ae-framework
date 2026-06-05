/**
 * Constrained condition-expression evaluator for conformance rules.
 *
 * This intentionally supports a small JavaScript-like expression subset used by
 * repository conformance rules without crossing from rule data into executable
 * JavaScript. Do not replace this parser with eval, Function, dynamic import,
 * or other ambient code-execution primitives.
 */

export interface ConformanceConditionContext {
  data: unknown;
  context: unknown;
  rule?: unknown;
  validators?: Record<string, unknown>;
  utils?: Record<string, unknown>;
}

export class ConformanceConditionDslError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'ConformanceConditionDslError';
  }
}

type TokenType =
  | 'identifier'
  | 'number'
  | 'string'
  | 'operator'
  | 'punctuation'
  | 'eof';

interface Token {
  type: TokenType;
  value: string;
  position: number;
}

type AstNode =
  | { kind: 'literal'; value: unknown }
  | { kind: 'identifier'; name: string }
  | { kind: 'member'; object: AstNode; property: string }
  | { kind: 'call'; callee: AstNode; args: AstNode[] }
  | { kind: 'unary'; operator: '!' | '+' | '-'; argument: AstNode }
  | { kind: 'binary'; operator: string; left: AstNode; right: AstNode };

const DANGEROUS_IDENTIFIERS = new Set([
  '__proto__',
  'constructor',
  'prototype',
  'process',
  'global',
  'globalThis',
  'require',
  'module',
  'Function',
  'eval',
  'import',
  'export',
  'class',
  'while',
  'for',
  'this',
]);

const ROOT_IDENTIFIERS = new Set([
  'data',
  'context',
  'rule',
  'validators',
  'utils',
  'true',
  'false',
  'null',
  'undefined',
  'Number',
  'Boolean',
  'String',
]);

const SAFE_BUILTINS = new Set(['Number', 'Boolean', 'String']);
const ALLOWED_VALIDATOR_HELPERS = new Set([
  'isEmail',
  'isUrl',
  'isNumber',
  'isString',
  'isBoolean',
  'isArray',
  'isObject',
  'hasLength',
  'inRange',
  'isBase64Like',
]);
const ALLOWED_UTILITY_HELPERS = new Set(['now', 'timestamp', 'uuid', 'hash']);
const MAX_EXPRESSION_LENGTH = 2_000;
const MAX_STRING_LITERAL_LENGTH = 1_000;

function isIdentifierStart(char: string): boolean {
  return /[A-Za-z_$]/.test(char);
}

function isIdentifierPart(char: string): boolean {
  return /[A-Za-z0-9_$]/.test(char);
}

function isLegacySymbolicExpression(expression: string): boolean {
  if (!/^[A-Za-z0-9_$\s&|]+$/.test(expression)) {
    return false;
  }
  const identifiers = expression.match(/[A-Za-z_$][A-Za-z0-9_$]*/g) ?? [];
  if (identifiers.length === 0) {
    return false;
  }
  return identifiers.every((identifier) => !ROOT_IDENTIFIERS.has(identifier) && !DANGEROUS_IDENTIFIERS.has(identifier));
}

function assertSafeIdentifier(identifier: string, label: string): void {
  if (DANGEROUS_IDENTIFIERS.has(identifier)) {
    throw new ConformanceConditionDslError(`${label} uses unsupported identifier: ${identifier}`);
  }
}

class Tokenizer {
  private readonly tokens: Token[] = [];
  private index = 0;

  constructor(private readonly input: string) {}

  tokenize(): Token[] {
    while (this.index < this.input.length) {
      const char = this.input[this.index]!;
      if (/\s/.test(char)) {
        this.index += 1;
        continue;
      }
      if (char === '"' || char === "'") {
        this.tokens.push(this.readString(char));
        continue;
      }
      if (/[0-9]/.test(char)) {
        this.tokens.push(this.readNumber());
        continue;
      }
      if (isIdentifierStart(char)) {
        this.tokens.push(this.readIdentifier());
        continue;
      }

      const position = this.index;
      const three = this.input.slice(this.index, this.index + 3);
      const two = this.input.slice(this.index, this.index + 2);
      if (three === '===' || three === '!==') {
        this.index += 3;
        this.tokens.push({ type: 'operator', value: three, position });
        continue;
      }
      if (['?.', '>=', '<=', '&&', '||', '??', '==', '!='].includes(two)) {
        if (two === '==' || two === '!=') {
          throw new ConformanceConditionDslError(`Loose equality operator '${two}' is unsupported; use strict equality instead`);
        }
        this.index += 2;
        this.tokens.push({ type: 'operator', value: two, position });
        continue;
      }
      if (['!', '<', '>', '+', '-', '*', '/', '%'].includes(char)) {
        this.index += 1;
        this.tokens.push({ type: 'operator', value: char, position });
        continue;
      }
      if (['.', '(', ')', ','].includes(char)) {
        this.index += 1;
        this.tokens.push({ type: 'punctuation', value: char, position });
        continue;
      }

      throw new ConformanceConditionDslError(`Unsupported expression character at ${position}: ${char}`);
    }
    this.tokens.push({ type: 'eof', value: '', position: this.input.length });
    return this.tokens;
  }

  private readIdentifier(): Token {
    const position = this.index;
    while (this.index < this.input.length && isIdentifierPart(this.input[this.index]!)) {
      this.index += 1;
    }
    const value = this.input.slice(position, this.index);
    assertSafeIdentifier(value, 'condition expression');
    return { type: 'identifier', value, position };
  }

  private readNumber(): Token {
    const position = this.index;
    while (this.index < this.input.length && /[0-9_]/.test(this.input[this.index]!)) {
      this.index += 1;
    }
    if (this.input[this.index] === '.') {
      this.index += 1;
      while (this.index < this.input.length && /[0-9_]/.test(this.input[this.index]!)) {
        this.index += 1;
      }
    }
    const value = this.input.slice(position, this.index).replace(/_/g, '');
    if (!/^\d+(?:\.\d+)?$/.test(value)) {
      throw new ConformanceConditionDslError(`Invalid numeric literal at ${position}`);
    }
    return { type: 'number', value, position };
  }

  private readString(quote: string): Token {
    const position = this.index;
    this.index += 1;
    let value = '';
    while (this.index < this.input.length) {
      const char = this.input[this.index]!;
      this.index += 1;
      if (char === quote) {
        if (value.length > MAX_STRING_LITERAL_LENGTH) {
          throw new ConformanceConditionDslError(`String literal at ${position} is too long`);
        }
        return { type: 'string', value, position };
      }
      if (char === '\\') {
        if (this.index >= this.input.length) {
          throw new ConformanceConditionDslError(`Unterminated escape sequence at ${position}`);
        }
        const escaped = this.input[this.index]!;
        this.index += 1;
        switch (escaped) {
          case '\\':
          case '"':
          case "'":
            value += escaped;
            break;
          case 'n':
            value += '\n';
            break;
          case 'r':
            value += '\r';
            break;
          case 't':
            value += '\t';
            break;
          default:
            throw new ConformanceConditionDslError(`Unsupported escape sequence at ${this.index - 2}`);
        }
      } else {
        if (char === '\n' || char === '\r') {
          throw new ConformanceConditionDslError(`String literal at ${position} must not span lines`);
        }
        value += char;
      }
    }
    throw new ConformanceConditionDslError(`Unterminated string literal at ${position}`);
  }
}

class Parser {
  private index = 0;

  constructor(private readonly tokens: Token[]) {}

  parse(): AstNode {
    const expression = this.parseLogicalOr();
    this.expect('eof');
    return expression;
  }

  private parseLogicalOr(): AstNode {
    let left = this.parseLogicalAnd();
    while (this.matchOperator('||')) {
      left = { kind: 'binary', operator: '||', left, right: this.parseLogicalAnd() };
    }
    return left;
  }

  private parseLogicalAnd(): AstNode {
    let left = this.parseNullish();
    while (this.matchOperator('&&')) {
      left = { kind: 'binary', operator: '&&', left, right: this.parseNullish() };
    }
    return left;
  }

  private parseNullish(): AstNode {
    let left = this.parseEquality();
    while (this.matchOperator('??')) {
      left = { kind: 'binary', operator: '??', left, right: this.parseEquality() };
    }
    return left;
  }

  private parseEquality(): AstNode {
    let left = this.parseRelational();
    while (true) {
      const operator = this.matchAnyOperator(['===', '!==']);
      if (!operator) return left;
      left = { kind: 'binary', operator, left, right: this.parseRelational() };
    }
  }

  private parseRelational(): AstNode {
    let left = this.parseAdditive();
    while (true) {
      const operator = this.matchAnyOperator(['>=', '<=', '>', '<']);
      if (!operator) return left;
      left = { kind: 'binary', operator, left, right: this.parseAdditive() };
    }
  }

  private parseAdditive(): AstNode {
    let left = this.parseMultiplicative();
    while (true) {
      const operator = this.matchAnyOperator(['+', '-']);
      if (!operator) return left;
      left = { kind: 'binary', operator, left, right: this.parseMultiplicative() };
    }
  }

  private parseMultiplicative(): AstNode {
    let left = this.parseUnary();
    while (true) {
      const operator = this.matchAnyOperator(['*', '/', '%']);
      if (!operator) return left;
      left = { kind: 'binary', operator, left, right: this.parseUnary() };
    }
  }

  private parseUnary(): AstNode {
    const operator = this.matchAnyOperator(['!', '+', '-']);
    if (operator) {
      return { kind: 'unary', operator: operator as '!' | '+' | '-', argument: this.parseUnary() };
    }
    return this.parseCallOrMember();
  }

  private parseCallOrMember(): AstNode {
    let node = this.parsePrimary();
    while (true) {
      if (this.matchPunctuation('.')) {
        const property = this.expect('identifier').value;
        assertSafeIdentifier(property, 'condition member expression');
        node = { kind: 'member', object: node, property };
        continue;
      }
      if (this.matchOperator('?.')) {
        const property = this.expect('identifier').value;
        assertSafeIdentifier(property, 'condition member expression');
        node = { kind: 'member', object: node, property };
        continue;
      }
      if (this.matchPunctuation('(')) {
        const args: AstNode[] = [];
        if (!this.matchPunctuation(')')) {
          do {
            args.push(this.parseLogicalOr());
          } while (this.matchPunctuation(','));
          this.expect('punctuation', ')');
        }
        node = { kind: 'call', callee: node, args };
        continue;
      }
      return node;
    }
  }

  private parsePrimary(): AstNode {
    const token = this.current();
    if (this.matchPunctuation('(')) {
      const expression = this.parseLogicalOr();
      this.expect('punctuation', ')');
      return expression;
    }
    if (token.type === 'identifier') {
      this.index += 1;
      switch (token.value) {
        case 'true':
          return { kind: 'literal', value: true };
        case 'false':
          return { kind: 'literal', value: false };
        case 'null':
          return { kind: 'literal', value: null };
        case 'undefined':
          return { kind: 'literal', value: undefined };
        default:
          return { kind: 'identifier', name: token.value };
      }
    }
    if (token.type === 'number') {
      this.index += 1;
      return { kind: 'literal', value: Number(token.value) };
    }
    if (token.type === 'string') {
      this.index += 1;
      return { kind: 'literal', value: token.value };
    }
    throw new ConformanceConditionDslError(`Expected expression at ${token.position}`);
  }

  private current(): Token {
    return this.tokens[this.index] ?? this.tokens[this.tokens.length - 1]!;
  }

  private matchOperator(value: string): boolean {
    const token = this.current();
    if (token.type === 'operator' && token.value === value) {
      this.index += 1;
      return true;
    }
    return false;
  }

  private matchAnyOperator(values: string[]): string | null {
    const token = this.current();
    if (token.type === 'operator' && values.includes(token.value)) {
      this.index += 1;
      return token.value;
    }
    return null;
  }

  private matchPunctuation(value: string): boolean {
    const token = this.current();
    if (token.type === 'punctuation' && token.value === value) {
      this.index += 1;
      return true;
    }
    return false;
  }

  private expect(type: TokenType, value?: string): Token {
    const token = this.current();
    if (token.type !== type || (value !== undefined && token.value !== value)) {
      const expected = value === undefined ? type : `${type} '${value}'`;
      throw new ConformanceConditionDslError(`Expected ${expected} at ${token.position}`);
    }
    this.index += 1;
    return token;
  }
}

function getMemberValue(object: unknown, property: string): unknown {
  assertSafeIdentifier(property, 'condition member expression');
  if (object === null || object === undefined) {
    return undefined;
  }
  if (typeof object === 'string' && property === 'length') {
    return object.length;
  }
  if (typeof object !== 'object' && typeof object !== 'function') {
    return undefined;
  }
  return (object as Record<string, unknown>)[property];
}

function isNullish(value: unknown): boolean {
  return value === null || value === undefined;
}

function callBuiltin(name: string, args: unknown[]): unknown {
  if (args.length !== 1) {
    throw new ConformanceConditionDslError(`${name} expects exactly one argument`);
  }
  switch (name) {
    case 'Number':
      return Number(args[0]);
    case 'Boolean':
      return Boolean(args[0]);
    case 'String':
      return String(args[0]);
    default:
      throw new ConformanceConditionDslError(`Unsupported function: ${name}`);
  }
}

function callHelper(rootName: string, helperName: string, args: unknown[], context: ConformanceConditionContext): unknown {
  const root = rootName === 'validators' ? context.validators : context.utils;
  const helper = root?.[helperName];
  if (typeof helper !== 'function') {
    throw new ConformanceConditionDslError(`Unsupported helper function: ${rootName}.${helperName}`);
  }
  return (helper as (...values: unknown[]) => unknown)(...args);
}

function validateIdentifierReference(name: string): void {
  assertSafeIdentifier(name, 'condition expression');
  if (!ROOT_IDENTIFIERS.has(name)) {
    throw new ConformanceConditionDslError(`Unknown identifier: ${name}`);
  }
}

function validateHelperCall(rootName: string, helperName: string): void {
  const allowed = rootName === 'validators' ? ALLOWED_VALIDATOR_HELPERS : ALLOWED_UTILITY_HELPERS;
  if (!allowed.has(helperName)) {
    throw new ConformanceConditionDslError(`Unsupported helper function: ${rootName}.${helperName}`);
  }
}

function validateAstNode(node: AstNode): void {
  switch (node.kind) {
    case 'literal':
      return;
    case 'identifier':
      validateIdentifierReference(node.name);
      return;
    case 'member':
      validateAstNode(node.object);
      assertSafeIdentifier(node.property, 'condition member expression');
      return;
    case 'call':
      for (const arg of node.args) {
        validateAstNode(arg);
      }
      if (node.callee.kind === 'identifier') {
        if (!SAFE_BUILTINS.has(node.callee.name)) {
          throw new ConformanceConditionDslError(`Unsupported function call: ${node.callee.name}`);
        }
        return;
      }
      if (
        node.callee.kind === 'member' &&
        node.callee.object.kind === 'identifier' &&
        (node.callee.object.name === 'validators' || node.callee.object.name === 'utils')
      ) {
        validateHelperCall(node.callee.object.name, node.callee.property);
        return;
      }
      throw new ConformanceConditionDslError('Only approved helper calls are supported in condition expressions');
    case 'unary':
      validateAstNode(node.argument);
      return;
    case 'binary':
      validateAstNode(node.left);
      validateAstNode(node.right);
      return;
    default:
      throw new ConformanceConditionDslError('Unsupported condition expression node');
  }
}

function evaluateNode(node: AstNode, context: ConformanceConditionContext): unknown {
  switch (node.kind) {
    case 'literal':
      return node.value;
    case 'identifier':
      assertSafeIdentifier(node.name, 'condition expression');
      if (node.name === 'data') return context.data;
      if (node.name === 'context') return context.context;
      if (node.name === 'rule') return context.rule;
      if (node.name === 'validators') return context.validators;
      if (node.name === 'utils') return context.utils;
      if (SAFE_BUILTINS.has(node.name)) return node.name;
      throw new ConformanceConditionDslError(`Unknown identifier: ${node.name}`);
    case 'member':
      return getMemberValue(evaluateNode(node.object, context), node.property);
    case 'call': {
      const args = node.args.map((arg) => evaluateNode(arg, context));
      if (node.callee.kind === 'identifier') {
        if (!SAFE_BUILTINS.has(node.callee.name)) {
          throw new ConformanceConditionDslError(`Unsupported function call: ${node.callee.name}`);
        }
        return callBuiltin(node.callee.name, args);
      }
      if (
        node.callee.kind === 'member' &&
        node.callee.object.kind === 'identifier' &&
        (node.callee.object.name === 'validators' || node.callee.object.name === 'utils')
      ) {
        return callHelper(node.callee.object.name, node.callee.property, args, context);
      }
      throw new ConformanceConditionDslError('Only approved helper calls are supported in condition expressions');
    }
    case 'unary': {
      const value = evaluateNode(node.argument, context);
      if (node.operator === '!') return !value;
      if (node.operator === '+') return Number(value);
      return -Number(value);
    }
    case 'binary': {
      if (node.operator === '&&') {
        const left = evaluateNode(node.left, context);
        return left ? evaluateNode(node.right, context) : left;
      }
      if (node.operator === '||') {
        const left = evaluateNode(node.left, context);
        return left ? left : evaluateNode(node.right, context);
      }
      if (node.operator === '??') {
        const left = evaluateNode(node.left, context);
        return isNullish(left) ? evaluateNode(node.right, context) : left;
      }

      const left = evaluateNode(node.left, context);
      const right = evaluateNode(node.right, context);
      switch (node.operator) {
        case '===':
          return left === right;
        case '!==':
          return left !== right;
        case '>=':
          return Number(left) >= Number(right);
        case '<=':
          return Number(left) <= Number(right);
        case '>':
          return Number(left) > Number(right);
        case '<':
          return Number(left) < Number(right);
        case '+':
          return typeof left === 'string' || typeof right === 'string'
            ? `${String(left)}${String(right)}`
            : Number(left) + Number(right);
        case '-':
          return Number(left) - Number(right);
        case '*':
          return Number(left) * Number(right);
        case '/':
          return Number(left) / Number(right);
        case '%':
          return Number(left) % Number(right);
        default:
          throw new ConformanceConditionDslError(`Unsupported operator: ${node.operator}`);
      }
    }
    default:
      throw new ConformanceConditionDslError('Unsupported condition expression node');
  }
}

export function createConditionValidators() {
  return {
    isBase64Like: (value: unknown): boolean => {
      if (typeof value !== 'string' || value.length === 0) return false;
      for (const char of value) {
        const code = char.charCodeAt(0);
        const isUpper = code >= 65 && code <= 90;
        const isLower = code >= 97 && code <= 122;
        const isDigit = code >= 48 && code <= 57;
        if (!isUpper && !isLower && !isDigit && char !== '+' && char !== '/' && char !== '=') {
          return false;
        }
      }
      return true;
    },
  };
}

export function evaluateConformanceConditionExpression(
  expression: string,
  context: ConformanceConditionContext,
): unknown {
  const trimmed = String(expression).trim();
  if (!trimmed) {
    return true;
  }
  if (trimmed.length > MAX_EXPRESSION_LENGTH) {
    throw new ConformanceConditionDslError('Condition expression is too long');
  }
  if (isLegacySymbolicExpression(trimmed)) {
    return true;
  }
  const ast = new Parser(new Tokenizer(trimmed).tokenize()).parse();
  return evaluateNode(ast, context);
}

export function validateConformanceConditionExpressionSyntax(expression: string): void {
  const trimmed = String(expression).trim();
  if (!trimmed) {
    throw new ConformanceConditionDslError('Condition expression is required');
  }
  if (trimmed.length > MAX_EXPRESSION_LENGTH) {
    throw new ConformanceConditionDslError('Condition expression is too long');
  }
  if (isLegacySymbolicExpression(trimmed)) {
    return;
  }
  validateAstNode(new Parser(new Tokenizer(trimmed).tokenize()).parse());
}
