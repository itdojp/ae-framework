import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';

describe('development compose scripts', () => {
  it('TGT-004-F002: scopes compose cleanup to the ae-framework-dev project without global prune', () => {
    const up = readFileSync('scripts/dev/dev_up.sh', 'utf8');
    const down = readFileSync('scripts/dev/dev_down.sh', 'utf8');

    expect(up).toContain('container::compose --project-name ae-framework-dev -f "$COMPOSE_FILE" up -d --build');
    expect(down).toContain('container::compose --project-name ae-framework-dev -f "$COMPOSE_FILE" down -v --remove-orphans');
    expect(`${up}\n${down}`).not.toMatch(/\b(?:docker|podman)\s+system\s+prune\b/);
    expect(`${up}\n${down}`).not.toMatch(/\b(?:docker|podman)\s+(?:container|image|volume|network)\s+prune\b/);
  });

  it('TGT-017-F001: requires dev database credentials through environment injection', () => {
    const up = readFileSync('scripts/dev/dev_up.sh', 'utf8');
    expect(up).toContain('AE_DEV_POSTGRES_USER');
    expect(up).toContain('AE_DEV_POSTGRES_PASSWORD');
    expect(up).toContain('AE_DEV_POSTGRES_DB');
    expect(up).toContain('require_dev_secret_env');
  });
});
