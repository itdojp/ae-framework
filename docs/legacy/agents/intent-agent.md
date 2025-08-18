# Intent Agent

The Intent Agent is a core component of the ae-framework Phase 1, responsible for requirements gathering, analysis, and intent extraction from multiple sources. It transforms raw requirements into structured formats that feed into subsequent phases of the architectural engineering process.

## Overview

The Intent Agent handles the crucial first phase of ae-framework by:

- **Requirements Gathering**: Collecting requirements from diverse sources including text, documents, conversations, issues, emails, and diagrams
- **Natural Language Processing**: Extracting structured requirements from unstructured natural language
- **User Story Generation**: Converting requirements into user stories with proper acceptance criteria
- **Use Case Creation**: Building comprehensive use case models with actors, flows, and exceptions
- **Domain Modeling**: Identifying entities, relationships, bounded contexts, and aggregates
- **Ambiguity Detection**: Finding and suggesting resolutions for ambiguous requirements
- **Risk Analysis**: Identifying potential risks and their mitigation strategies
- **Assumption Management**: Tracking assumptions that need validation
- **Stakeholder Analysis**: Analyzing stakeholder concerns and detecting conflicts
- **Traceability**: Creating links between requirements and downstream artifacts
- **Specification Generation**: Creating templates for Gherkin, OpenAPI, AsyncAPI, and GraphQL specifications

## Architecture

### Core Components

```typescript
IntentAgent
├── Requirements Processing
│   ├── Source Extraction
│   ├── Natural Language Analysis
│   └── Requirement Categorization
├── Analysis & Modeling
│   ├── User Story Generation
│   ├── Use Case Creation
│   ├── Domain Model Building
│   └── Stakeholder Analysis
├── Quality Assurance
│   ├── Ambiguity Detection
│   ├── Completeness Validation
│   └── Risk Assessment
└── Output Generation
    ├── Specification Templates
    ├── Traceability Matrix
    └── Structured Reports
```

### MCP Server Integration

The Intent Agent is exposed as an MCP (Model Context Protocol) server, providing tools that can be used by AI assistants and other systems. The MCP server wrapper (`src/mcp-server/intent-server.ts`) exposes the following tools:

- `analyze_intent`: Complete intent analysis workflow
- `extract_from_natural_language`: Extract requirements from text
- `create_user_stories`: Generate user stories from requirements
- `build_domain_model`: Create domain models with entities and relationships
- `detect_ambiguities`: Identify ambiguous requirements
- `validate_completeness`: Check requirement coverage
- `generate_specification_templates`: Create specification templates
- `prioritize_requirements`: Apply MoSCoW prioritization
- `generate_acceptance_criteria`: Create acceptance criteria
- `analyze_stakeholder_concerns`: Analyze stakeholder conflicts

## Usage

### Running the Intent Agent

#### As MCP Server
```bash
npm run intent-agent
```

#### Direct Usage
```typescript
import { IntentAgent, IntentAnalysisRequest } from './src/agents/intent-agent.js';

const agent = new IntentAgent();

const request: IntentAnalysisRequest = {
  sources: [
    {
      type: 'text',
      content: 'Users need to be able to reserve inventory items',
      metadata: {
        author: 'Product Manager',
        priority: 'high'
      }
    }
  ],
  context: {
    domain: 'Inventory Management',
    existingSystem: false
  },
  analysisDepth: 'comprehensive'
};

const result = await agent.analyzeIntent(request);
```

### Input Sources

The Intent Agent can process various types of requirement sources:

#### Text Sources
```typescript
{
  type: 'text',
  content: 'The system should allow users to search for products',
  metadata: {
    author: 'Business Analyst',
    date: new Date(),
    priority: 'high',
    tags: ['search', 'products']
  }
}
```

#### Document Sources
```typescript
{
  type: 'document',
  content: `
Requirements Document
1. Users must authenticate before accessing the system
2. Products should be searchable by category and name
3. Inventory levels must be tracked in real-time
  `,
  metadata: {
    author: 'Requirements Team'
  }
}
```

#### Conversation Sources
```typescript
{
  type: 'conversation',
  content: `
PM: We need a way for customers to reserve items
Dev: How long should reservations last?
PM: I think 30 minutes is reasonable
Customer: I want to be notified when items are available
  `,
  metadata: {
    date: new Date(),
    tags: ['stakeholder-meeting']
  }
}
```

#### Issue/Ticket Sources
```typescript
{
  type: 'issue',
  content: `
## User Story
As a customer, I want to reserve inventory items so that I can ensure availability before purchase.

## Acceptance Criteria
- Reservations last 30 minutes
- Users receive confirmation
- Items are locked during reservation
  `,
  metadata: {
    author: 'Product Owner',
    references: ['TICKET-123']
  }
}
```

### Project Context

Provide domain context to improve analysis quality:

```typescript
const context: ProjectContext = {
  domain: 'E-commerce Inventory Management',
  existingSystem: true,
  constraints: [
    {
      type: 'technical',
      description: 'Must integrate with existing ERP system',
      impact: 'high'
    },
    {
      type: 'business',
      description: 'Go-live deadline is Q1 2024',
      impact: 'medium'
    }
  ],
  stakeholders: [
    {
      name: 'Product Manager',
      role: 'Product Owner',
      concerns: ['User experience', 'Feature completeness'],
      influenceLevel: 'high'
    },
    {
      name: 'Operations Team',
      role: 'End User',
      concerns: ['System reliability', 'Performance'],
      influenceLevel: 'medium'
    }
  ],
  glossary: [
    {
      term: 'Reservation',
      definition: 'Temporary hold on inventory items',
      context: 'Prevents double-booking of limited inventory'
    }
  ]
}
```

## Output Formats

### Complete Analysis Result

The `analyzeIntent` method returns a comprehensive analysis:

```typescript
interface IntentAnalysisResult {
  requirements: Requirement[];           // Structured requirements
  userStories: UserStory[];             // Generated user stories
  useCases: UseCase[];                  // Use case models
  constraints: Constraint[];            // System constraints
  assumptions: Assumption[];            // Identified assumptions
  risks: Risk[];                       // Risk analysis
  domainModel: DomainModel;            // Domain entities and relationships
  ambiguities: Ambiguity[];            // Ambiguous elements
  suggestions: string[];               // Improvement recommendations
  traceability: RequirementTrace[];    // Traceability links
}
```

### Requirements Structure

```typescript
interface Requirement {
  id: string;                          // Unique identifier (REQ-001)
  type: 'functional' | 'non-functional' | 'business' | 'technical';
  category: string;                    // authentication, performance, etc.
  description: string;                 // Requirement description
  rationale?: string;                  // Why this requirement exists
  priority: 'must' | 'should' | 'could' | 'wont';  // MoSCoW priority
  acceptance: AcceptanceCriteria[];    // Given-When-Then criteria
  source: string;                      // Origin of requirement
  status: 'draft' | 'reviewed' | 'approved' | 'implemented';
  dependencies?: string[];             // Related requirements
}
```

### User Stories

```typescript
interface UserStory {
  id: string;                          // US-001
  title: string;                       // Short descriptive title
  narrative: {
    asA: string;                       // User role
    iWant: string;                     // Desired functionality
    soThat: string;                    // Business value
  };
  acceptance: AcceptanceCriteria[];    // Acceptance criteria
  points?: number;                     // Story points
  priority: 'high' | 'medium' | 'low';
  requirements: string[];              // Linked requirements
}
```

### Domain Model

```typescript
interface DomainModel {
  entities: Entity[];                  // Domain entities
  relationships: Relationship[];       // Entity relationships
  boundedContexts: BoundedContext[];  // Domain boundaries
  aggregates: Aggregate[];            // Aggregate roots
}

interface Entity {
  name: string;                       // Entity name
  attributes: Attribute[];            // Properties
  behaviors: string[];                // Methods/operations
  invariants: string[];               // Business rules
}
```

### Ambiguity Detection

```typescript
interface Ambiguity {
  text: string;                       // Ambiguous text
  type: 'vague' | 'conflicting' | 'incomplete' | 'undefined';
  location: string;                   // Where found
  suggestion: string;                 // Recommended resolution
  severity: 'high' | 'medium' | 'low';
}
```

## Quality Assurance Features

### Completeness Validation

The agent validates requirement completeness across essential categories:

- Authentication & Authorization
- Data Validation
- Error Handling
- Logging & Monitoring
- Performance
- Security
- Usability

```typescript
const validation = await agent.validateCompleteness(requirements);
// Returns: { complete: boolean, missing: string[], coverage: number }
```

### Ambiguity Detection

Automatically identifies:
- **Vague terms**: "fast", "good", "many"
- **Ambiguous qualifiers**: "maybe", "possibly", "soon"
- **Undefined terms**: Context-specific jargon
- **Conflicting statements**: Contradictory requirements

### Risk Analysis

Identifies common risks:
- Performance bottlenecks
- Security vulnerabilities
- Integration challenges
- Resource constraints
- Technical debt

### Stakeholder Conflict Detection

Analyzes stakeholder concerns to identify:
- Conflicting priorities
- Unaddressed concerns
- Influence mapping
- Communication gaps

## Specification Template Generation

### Gherkin Scenarios
```gherkin
Feature: Inventory Reservation
  Scenario: Reserve available item
    Given an item is available in inventory
    When a user reserves the item
    Then the item is locked for 30 minutes
    And the user receives a confirmation
```

### OpenAPI Specification
```yaml
openapi: 3.0.0
info:
  title: Inventory API
  version: 1.0.0
paths:
  /reservations:
    post:
      summary: Create item reservation
      requestBody:
        content:
          application/json:
            schema:
              $ref: '#/components/schemas/ReservationRequest'
```

### AsyncAPI Specification
```yaml
asyncapi: 2.0.0
info:
  title: Inventory Events
  version: 1.0.0
channels:
  inventory/reserved:
    publish:
      message:
        $ref: '#/components/messages/ItemReserved'
```

### GraphQL Schema
```graphql
type Query {
  inventory: [InventoryItem!]!
  reservations: [Reservation!]!
}

type Mutation {
  reserveItem(itemId: ID!, duration: Int): Reservation!
}

type InventoryItem {
  id: ID!
  name: String!
  available: Boolean!
}
```

## Integration with ae-framework

The Intent Agent serves as the foundation for the entire ae-framework workflow:

### Phase 1 → Phase 2 Integration
- **Requirements** → Architecture Design
- **Domain Model** → System Architecture
- **Constraints** → Architecture Decisions
- **Use Cases** → Component Design

### Phase 1 → Phase 3 Integration
- **Acceptance Criteria** → Test Cases
- **Specification Templates** → Test Automation
- **Traceability** → Test Coverage

### Phase 1 → Phase 4 Integration
- **Requirements** → Implementation Tasks
- **Domain Model** → Code Structure
- **Constraints** → Implementation Decisions

## Best Practices

### Requirements Gathering
1. **Use Multiple Sources**: Combine documents, conversations, and issues
2. **Provide Context**: Include domain information and constraints
3. **Validate Stakeholders**: Ensure all key stakeholders are represented
4. **Document Assumptions**: Make implicit assumptions explicit

### Analysis Configuration
1. **Choose Appropriate Depth**: 
   - `basic`: Quick analysis for early stages
   - `detailed`: Standard comprehensive analysis
   - `comprehensive`: Deep analysis with extensive modeling
2. **Select Output Format**:
   - `structured`: JSON output for tool integration
   - `narrative`: Human-readable reports
   - `both`: Complete documentation

### Quality Assurance
1. **Address High-Severity Ambiguities**: Resolve unclear requirements early
2. **Validate Completeness**: Ensure all essential categories are covered
3. **Review Stakeholder Conflicts**: Resolve conflicting concerns
4. **Assess Risks**: Plan mitigation for high-impact risks

## Performance Considerations

### Scalability
- Processes multiple requirement sources concurrently
- Caches analysis results for iterative refinement
- Supports incremental updates to existing analyses

### Memory Usage
- Streams large documents for processing
- Garbage collects intermediate analysis artifacts
- Optimizes entity relationship graph storage

### Processing Time
- **Basic Analysis**: < 1 second for small inputs
- **Detailed Analysis**: 2-5 seconds for medium complexity
- **Comprehensive Analysis**: 5-15 seconds for large, complex inputs

## Error Handling

The Intent Agent provides comprehensive error handling:

### Input Validation Errors
```typescript
// Invalid source type
throw new Error('Unsupported source type: unknown');

// Missing required fields
throw new Error('Source content is required');

// Invalid analysis depth
throw new Error('Analysis depth must be basic, detailed, or comprehensive');
```

### Processing Errors
```typescript
// Natural language processing failures
throw new Error('Failed to extract requirements from text');

// Domain model building errors
throw new Error('Unable to identify entity relationships');

// Ambiguity detection failures
throw new Error('Ambiguity analysis failed for source');
```

### MCP Server Errors
```typescript
// Tool execution errors
throw new McpError(ErrorCode.InternalError, 'Analysis failed');

// Unknown tool requests
throw new McpError(ErrorCode.MethodNotFound, 'Unknown tool');
```

## Testing

### Unit Tests
```bash
npm test -- --grep "IntentAgent"
```

### Integration Tests
```bash
npm run bdd -- --tags @intent-agent
```

### Property-Based Tests
```bash
npm run pbt -- --grep "intent-agent"
```

## Configuration

### Environment Variables
```bash
# Log level for Intent Agent
INTENT_AGENT_LOG_LEVEL=debug

# Analysis timeout (ms)
INTENT_ANALYSIS_TIMEOUT=30000

# Maximum concurrent analyses
MAX_CONCURRENT_ANALYSES=5
```

### Analysis Configuration
```typescript
interface AnalysisConfig {
  enableCaching: boolean;           // Cache analysis results
  maxSourceSize: number;           // Maximum source content size
  timeoutMs: number;               // Analysis timeout
  concurrency: number;             // Concurrent processing limit
}
```

## Troubleshooting

### Common Issues

#### "Failed to extract requirements"
- **Cause**: Source content is too ambiguous or unstructured
- **Solution**: Provide more structured input or use conversation type for informal content

#### "Domain model is incomplete"
- **Cause**: Requirements lack sufficient entity information
- **Solution**: Add more detailed functional requirements or provide domain context

#### "High ambiguity count"
- **Cause**: Requirements contain vague or conflicting language
- **Solution**: Review and clarify ambiguous terms identified in the analysis

#### "Stakeholder conflicts detected"
- **Cause**: Different stakeholders have contradictory concerns
- **Solution**: Facilitate stakeholder meetings to resolve conflicts

### Debug Mode
```bash
DEBUG=intent-agent:* npm run intent-agent
```

### Logging
The Intent Agent uses structured logging for troubleshooting:
```typescript
logger.info('Starting intent analysis', { 
  sourceCount: sources.length,
  analysisDepth,
  domain: context?.domain 
});

logger.debug('Extracted requirements', { 
  count: requirements.length,
  categories: [...new Set(requirements.map(r => r.category))]
});

logger.warn('Ambiguities detected', { 
  count: ambiguities.length,
  highSeverity: ambiguities.filter(a => a.severity === 'high').length
});
```

## Contributing

### Adding New Source Types
1. Extend `RequirementSource` interface
2. Implement parser in `extractFromSource()` method
3. Add validation logic
4. Update MCP server schema
5. Add tests and documentation

### Extending Analysis Capabilities
1. Add new analysis method to `IntentAgent` class
2. Update `IntentAnalysisResult` interface
3. Expose as MCP tool if needed
4. Add comprehensive tests
5. Update documentation

### Improving Quality Assurance
1. Add new detection patterns
2. Enhance existing validators
3. Improve suggestion algorithms
4. Add domain-specific rules
5. Update test coverage

## Roadmap

### Short Term
- [ ] Enhanced natural language processing with ML models
- [ ] Support for additional source formats (PDF, Word, Excel)
- [ ] Real-time collaboration features
- [ ] Advanced risk assessment algorithms

### Medium Term
- [ ] Integration with external requirement management tools
- [ ] Automated stakeholder communication
- [ ] Visual domain modeling interface
- [ ] Requirements change impact analysis

### Long Term
- [ ] AI-powered requirement generation
- [ ] Predictive quality analysis
- [ ] Cross-project requirement reuse
- [ ] Automated specification generation

## License

Part of ae-framework - MIT Licensed

## Support

For questions and support:
- Create issues in the ae-framework repository
- Review existing documentation
- Consult the troubleshooting guide
- Check the FAQ section

---

*This documentation is maintained as part of the ae-framework project. Last updated: 2025*