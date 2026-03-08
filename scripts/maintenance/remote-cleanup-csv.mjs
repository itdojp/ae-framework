export const csvEscape = (value) => {
  const stringValue = String(value ?? '');
  if (!/[",\n\r]/.test(stringValue)) return stringValue;
  return `"${stringValue.replace(/"/g, '""')}"`;
};

export const renderCsv = (headers, rows) => {
  const lines = [headers.map(csvEscape).join(',')];
  for (const row of rows) {
    lines.push(headers.map((header) => csvEscape(row?.[header] ?? '')).join(','));
  }
  return `${lines.join('\n')}\n`;
};

export const parseCsvRows = (input) => {
  const rows = [];
  let row = [];
  let field = '';
  let inQuotes = false;

  for (let index = 0; index < input.length; index += 1) {
    const char = input[index];
    if (inQuotes) {
      if (char === '"') {
        if (input[index + 1] === '"') {
          field += '"';
          index += 1;
        } else {
          inQuotes = false;
        }
      } else {
        field += char;
      }
      continue;
    }

    if (char === '"') {
      inQuotes = true;
      continue;
    }
    if (char === ',') {
      row.push(field);
      field = '';
      continue;
    }
    if (char === '\n') {
      row.push(field);
      rows.push(row);
      row = [];
      field = '';
      continue;
    }
    if (char === '\r') {
      if (input[index + 1] === '\n') index += 1;
      row.push(field);
      rows.push(row);
      row = [];
      field = '';
      continue;
    }
    field += char;
  }

  if (inQuotes) {
    throw new Error('CSV parse error: unmatched quote');
  }

  if (field.length > 0 || row.length > 0) {
    row.push(field);
    rows.push(row);
  }

  return rows.filter((currentRow) => currentRow.some((cell) => String(cell || '').length > 0));
};

export const parseCsvRecords = (input) => {
  const rows = parseCsvRows(input);
  if (rows.length === 0) return [];

  const [headers, ...values] = rows;
  return values
    .filter((row) => row.some((cell) => String(cell || '').length > 0))
    .map((row) =>
      Object.fromEntries(headers.map((header, index) => [String(header || '').trim(), row[index] ?? ''])),
    );
};
