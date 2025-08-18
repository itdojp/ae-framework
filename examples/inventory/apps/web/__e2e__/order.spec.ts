import { test, expect } from '@playwright/test';

test.describe('Order Management', () => {
  test.beforeEach(async ({ page }) => {
    // Navigate to orders page
    await page.goto('/order');
  });

  test('should display orders list page', async ({ page }) => {
    // Check page title
    await expect(page).toHaveTitle(/Orders/);
    
    // Check main heading
    await expect(page.getByRole('heading', { name: 'Orders' })).toBeVisible();
    
    // Check "Add New Order" button
    await expect(page.getByRole('button', { name: 'Add New Order' })).toBeVisible();
    
    // Check search input
    await expect(page.getByPlaceholder('Search orders...')).toBeVisible();
  });

  test('should navigate to create new order page', async ({ page }) => {
    // Click "Add New Order" button
    await page.getByRole('button', { name: 'Add New Order' }).click();
    
    // Should navigate to new order page
    await expect(page).toHaveURL('/order/new');
    
    // Check page heading
    await expect(page.getByRole('heading', { name: 'Create New Order' })).toBeVisible();
    
    // Check form is present
    await expect(page.getByLabel('Order Number *')).toBeVisible();
    await expect(page.getByLabel('Customer Id *')).toBeVisible();
    await expect(page.getByLabel('Customer Email *')).toBeVisible();
    await expect(page.getByLabel('Status *')).toBeVisible();
    await expect(page.getByLabel('Items *')).toBeVisible();
    await expect(page.getByLabel('Subtotal *')).toBeVisible();
    await expect(page.getByLabel('Tax Amount *')).toBeVisible();
    await expect(page.getByLabel('Shipping Amount *')).toBeVisible();
    await expect(page.getByLabel('Total *')).toBeVisible();
    await expect(page.getByLabel('Shipping Address *')).toBeVisible();
    await expect(page.getByLabel('Order Date *')).toBeVisible();
  });

  test('should create a new order successfully', async ({ page }) => {
    // Navigate to create page
    await page.goto('/order/new');
    
    // Fill out the form
    await page.getByLabel('Order Number *').fill('Test orderNumber');
    await page.getByLabel('Customer Id *').fill('Test customerId');
    await page.getByLabel('Customer Email *').fill('Test customerEmail');
    await page.getByLabel('Status *').fill('Test status');
    await page.getByLabel('Items *').fill('test');
    await page.getByLabel('Subtotal *').fill('100');
    await page.getByLabel('Tax Amount *').fill('100');
    await page.getByLabel('Shipping Amount *').fill('100');
    await page.getByLabel('Total *').fill('100');
    await page.getByLabel('Shipping Address *').fill('test');
    await page.getByLabel('Order Date *').fill('2024-01-01');
    
    await page.getByLabel('Notes').fill('Test notes');
    await page.getByLabel('Shipped Date').fill('2024-01-01');
    await page.getByLabel('Delivered Date').fill('2024-01-01');
    
    // Submit form
    await page.getByRole('button', { name: 'Create Order' }).click();
    
    // Should redirect to orders list
    await expect(page).toHaveURL('/order');
    
    // Should show success message or new order in list
  });

  test('should show validation errors for invalid form data', async ({ page }) => {
    // Navigate to create page
    await page.goto('/order/new');
    
    // Submit form without filling required fields
    await page.getByRole('button', { name: 'Create Order' }).click();
    
    // Should show validation errors
    await expect(page.getByText(/Order Number.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Customer Id.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Customer Email.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Status.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Items.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Subtotal.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Tax Amount.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Shipping Amount.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Total.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Shipping Address.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Order Date.*(required|必須)/i)).toBeVisible();
  });

  test('should search orders', async ({ page }) => {
    // Search for orders
    const searchTerm = 'order';
    await page.getByPlaceholder('Search orders...').fill(searchTerm);
    
    // Wait for search results
    await page.waitForTimeout(500);
    
    // Check that search was performed (URL should contain search parameter)
    await expect(page).toHaveURL(new RegExp(`search=${searchTerm}`));
  });

  test('should filter orders by status', async ({ page }) => {
    // Use status filter
    await page.selectOption('select', 'pending');
    
    // Wait for filter results
    await page.waitForTimeout(500);
    
    // Check that filter was applied (URL should contain filter parameter)
    await expect(page).toHaveURL(new RegExp(`filter=pending`));
  });

  test('should view order details', async ({ page }) => {
    // Assuming there's at least one order in the list
    const firstCard = page.locator('[data-testid="order-card"]').first();
    
    if (await firstCard.count() > 0) {
      await firstCard.getByText('View Details').click();
      
      // Should navigate to detail page
      await expect(page).toHaveURL(new RegExp(`/order/[a-zA-Z0-9-]+`));
      
      // Check detail page elements
      await expect(page.getByText('Back to Orders')).toBeVisible();
      await expect(page.getByRole('button', { name: 'Edit' })).toBeVisible();
      await expect(page.getByRole('button', { name: 'Delete' })).toBeVisible();
    }
  });

  test('should edit order details', async ({ page }) => {
    // Navigate to first order detail page
    const firstCard = page.locator('[data-testid="order-card"]').first();
    
    if (await firstCard.count() > 0) {
      await firstCard.getByText('View Details').click();
      
      // Click edit button
      await page.getByRole('button', { name: 'Edit' }).click();
      
      // Form should be visible in edit mode
      await expect(page.getByLabel('Order Number')).toBeVisible();
      await expect(page.getByLabel('Customer Id')).toBeVisible();
      await expect(page.getByLabel('Customer Email')).toBeVisible();
      await expect(page.getByLabel('Status')).toBeVisible();
      await expect(page.getByLabel('Items')).toBeVisible();
      await expect(page.getByLabel('Subtotal')).toBeVisible();
      await expect(page.getByLabel('Tax Amount')).toBeVisible();
      await expect(page.getByLabel('Shipping Amount')).toBeVisible();
      await expect(page.getByLabel('Total')).toBeVisible();
      await expect(page.getByLabel('Shipping Address')).toBeVisible();
      await expect(page.getByLabel('Notes')).toBeVisible();
      await expect(page.getByLabel('Order Date')).toBeVisible();
      await expect(page.getByLabel('Shipped Date')).toBeVisible();
      await expect(page.getByLabel('Delivered Date')).toBeVisible();
      
      // Update a field
      
      // Submit update
      await page.getByRole('button', { name: 'Update Order' }).click();
      
      // Should show updated value
    }
  });

  test('should handle order deletion with confirmation', async ({ page }) => {
    // Navigate to first order detail page
    const firstCard = page.locator('[data-testid="order-card"]').first();
    
    if (await firstCard.count() > 0) {
      await firstCard.getByText('View Details').click();
      
      // Set up dialog handler for confirmation
      page.on('dialog', dialog => dialog.accept());
      
      // Click delete button
      await page.getByRole('button', { name: 'Delete' }).click();
      
      // Should redirect to orders list
      await expect(page).toHaveURL('/order');
    }
  });
});