// Template: copy to specs/bdd/steps/<feature>.steps.js
import assert from 'node:assert/strict';
import { Before, Given, When, Then } from '@cucumber/cucumber';

class TemplateWorld {
  constructor() {
    this.state = {};
    this.lastResult = null;
  }
}

Before(function () {
  Object.assign(this, new TemplateWorld());
});

Given('<precondition>', async function () {
  // Arrange
});

When('<action>', async function () {
  // Act
  this.lastResult = null;
});

Then('<expected outcome>', async function () {
  // Assert
  assert.ok(this.lastResult !== null);
});
