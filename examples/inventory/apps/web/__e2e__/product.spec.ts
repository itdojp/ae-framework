import { test, expect } from '@playwright/test';

test.describe('Product Management', () => {
  test.beforeEach(async ({ page }) => {
    // Navigate to products page
    await page.goto('/product');
  });

  test('should display products list page', async ({ page }) => {
    // Check page title
    await expect(page).toHaveTitle(/Products/);
    
    // Check main heading
    await expect(page.getByRole('heading', { name: 'Products' })).toBeVisible();
    
    // Check "Add New Product" button
    await expect(page.getByRole('button', { name: 'Add New Product' })).toBeVisible();
    
    // Check search input
    await expect(page.getByPlaceholder('Search products...')).toBeVisible();
  });

  test('should navigate to create new product page', async ({ page }) => {
    // Click "Add New Product" button
    await page.getByRole('button', { name: 'Add New Product' }).click();
    
    // Should navigate to new product page
    await expect(page).toHaveURL('/product/new');
    
    // Check page heading
    await expect(page.getByRole('heading', { name: 'Create New Product' })).toBeVisible();
    
    // Check form is present
    await expect(page.getByLabel('Name *')).toBeVisible();
    await expect(page.getByLabel('Price *')).toBeVisible();
    await expect(page.getByLabel('Stock *')).toBeVisible();
    await expect(page.getByLabel('Low Stock Threshold *')).toBeVisible();
    await expect(page.getByLabel('Category *')).toBeVisible();
    await expect(page.getByLabel('Sku *')).toBeVisible();
    await expect(page.getByLabel('Active *')).toBeVisible();
  });

  test('should create a new product successfully', async ({ page }) => {
    // Navigate to create page
    await page.goto('/product/new');
    
    // Fill out the form
    await page.getByLabel('Name *').fill('Test name');
    await page.getByLabel('Price *').fill('100');
    await page.getByLabel('Stock *').fill('100');
    await page.getByLabel('Low Stock Threshold *').fill('100');
    await page.getByLabel('Category *').fill('Test category');
    await page.getByLabel('Sku *').fill('Test sku');
    await page.getByLabel('Active *').fill('true');
    
    await page.getByLabel('Description').fill('Test description');
    await page.getByLabel('Weight').fill('100');
    await page.getByLabel('Dimensions').fill('test');
    await page.getByLabel('Tags').fill('test');
    
    // Submit form
    await page.getByRole('button', { name: 'Create Product' }).click();
    
    // Should redirect to products list
    await expect(page).toHaveURL('/product');
    
    // Should show success message or new product in list
    await expect(page.getByText('Test name')).toBeVisible();
  });

  test('should show validation errors for invalid form data', async ({ page }) => {
    // Navigate to create page
    await page.goto('/product/new');
    
    // Submit form without filling required fields
    await page.getByRole('button', { name: 'Create Product' }).click();
    
    // Should show validation errors
    await expect(page.getByText(/Name.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Price.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Stock.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Low Stock Threshold.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Category.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Sku.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Active.*(required|必須)/i)).toBeVisible();
  });

  test('should search products', async ({ page }) => {
    // Search for products
    const searchTerm = 'test';
    await page.getByPlaceholder('Search products...').fill(searchTerm);
    
    // Wait for search results
    await page.waitForTimeout(500);
    
    // Check that search was performed (URL should contain search parameter)
    await expect(page).toHaveURL(new RegExp(`search=${searchTerm}`));
  });

  test('should filter products by status', async ({ page }) => {
    // Use status filter
    await page.selectOption('select', '');
    
    // Wait for filter results
    await page.waitForTimeout(500);
    
    // Check that filter was applied (URL should contain filter parameter)
    await expect(page).toHaveURL(new RegExp(`filter=`));
  });

  test('should view product details', async ({ page }) => {
    // Assuming there's at least one product in the list
    const firstCard = page.locator('[data-testid="product-card"]').first();
    
    if (await firstCard.count() > 0) {
      await firstCard.getByText('View Details').click();
      
      // Should navigate to detail page
      await expect(page).toHaveURL(new RegExp(`/product/[a-zA-Z0-9-]+`));
      
      // Check detail page elements
      await expect(page.getByText('Back to Products')).toBeVisible();
      await expect(page.getByRole('button', { name: 'Edit' })).toBeVisible();
      await expect(page.getByRole('button', { name: 'Delete' })).toBeVisible();
    }
  });

  test('should edit product details', async ({ page }) => {
    // Navigate to first product detail page
    const firstCard = page.locator('[data-testid="product-card"]').first();
    
    if (await firstCard.count() > 0) {
      await firstCard.getByText('View Details').click();
      
      // Click edit button
      await page.getByRole('button', { name: 'Edit' }).click();
      
      // Form should be visible in edit mode
      await expect(page.getByLabel('Name')).toBeVisible();
      await expect(page.getByLabel('Description')).toBeVisible();
      await expect(page.getByLabel('Price')).toBeVisible();
      await expect(page.getByLabel('Stock')).toBeVisible();
      await expect(page.getByLabel('Low Stock Threshold')).toBeVisible();
      await expect(page.getByLabel('Category')).toBeVisible();
      await expect(page.getByLabel('Sku')).toBeVisible();
      await expect(page.getByLabel('Weight')).toBeVisible();
      await expect(page.getByLabel('Dimensions')).toBeVisible();
      await expect(page.getByLabel('Active')).toBeVisible();
      await expect(page.getByLabel('Tags')).toBeVisible();
      
      // Update a field
      await page.getByLabel('Name').fill('Updated Name');
      
      // Submit update
      await page.getByRole('button', { name: 'Update Product' }).click();
      
      // Should show updated value
      await expect(page.getByText('Updated Name')).toBeVisible();
    }
  });

  test('should handle product deletion with confirmation', async ({ page }) => {
    // Navigate to first product detail page
    const firstCard = page.locator('[data-testid="product-card"]').first();
    
    if (await firstCard.count() > 0) {
      await firstCard.getByText('View Details').click();
      
      // Set up dialog handler for confirmation
      page.on('dialog', dialog => dialog.accept());
      
      // Click delete button
      await page.getByRole('button', { name: 'Delete' }).click();
      
      // Should redirect to products list
      await expect(page).toHaveURL('/product');
    }
  });
});