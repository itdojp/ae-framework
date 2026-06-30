import assert from 'node:assert/strict';
import { Given, When, Then } from '@cucumber/cucumber';

Given('a reservation quantity of {int}', function (quantity) {
  this.quantity = quantity;
});

When('the minimum activation sample validates the quantity', function () {
  this.validationResult = Number.isInteger(this.quantity) && this.quantity > 0;
});

Then('the reservation quantity remains positive', function () {
  assert.equal(this.validationResult, true);
  assert.ok(this.quantity > 0);
});
