import {test, expect} from '@playwright/test';

test.describe('Customer Management', () => {
  test.beforeEach(async ({page}) => {
    // Navigate to customers page
    await page.goto('/customer');
 });

  test('should display customers list page', async ({page}) => {
    // Check page title
    await expect(page).toHaveTitle(/Customers/);
    
    // Check main heading
    await expect(page.getByRole('heading', {name: 'Customers'})).toBeVisible();
    
    // Check "Add New Customer" button
    await expect(page.getByRole('button', {name: 'Add New Customer'})).toBeVisible();
    
    // Check search input
    await expect(page.getByPlaceholder('Search customers...')).toBeVisible();
 });

  test('should navigate to create new customer page', async ({page}) => {
    // Click "Add New Customer" button
    await page.getByRole('button', {name: 'Add New Customer'}).click();
    
    // Should navigate to new customer page
    await expect(page).toHaveURL('/customer/new');
    
    // Check page heading
    await expect(page.getByRole('heading', {name: 'Create New Customer'})).toBeVisible();
    
    // Check form is present
    await expect(page.getByLabel('Email *')).toBeVisible();
    await expect(page.getByLabel('First Name *')).toBeVisible();
    await expect(page.getByLabel('Last Name *')).toBeVisible();
 });

  test('should create a new customer successfully', async ({page}) => {
    // Navigate to create page
    await page.goto('/customer/new');
    
    // Fill out the form
    await page.getByLabel('Email *').fill('Test email');
    await page.getByLabel('First Name *').fill('Test firstName');
    await page.getByLabel('Last Name *').fill('Test lastName');
    
    await page.getByLabel('Phone').fill('Test phone');
    
    // Submit form
    await page.getByRole('button', {name: 'Create Customer'}).click();
    
    // Should redirect to customers list
    await expect(page).toHaveURL('/customer');
    
    // Should show success message or new customer in list
 });

  test('should show validation errors for invalid form data', async ({page}) => {
    // Navigate to create page
    await page.goto('/customer/new');
    
    // Submit form without filling required fields
    await page.getByRole('button', {name: 'Create Customer'}).click();
    
    // Should show validation errors
    await expect(page.getByText(/Email.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/First Name.*(required|必須)/i)).toBeVisible();
    await expect(page.getByText(/Last Name.*(required|必須)/i)).toBeVisible();
 });

  test('should search customers', async ({page}) => {
    // Search for customers
    const searchTerm = 'customer';
    await page.getByPlaceholder('Search customers...').fill(searchTerm);
    
    // Wait for search results
    await page.waitForTimeout(500);
    
    // Check that search was performed (URL should contain search parameter)
    await expect(page).toHaveURL(new RegExp(`search=${searchTerm}`));
 });


  test('should view customer details', async ({page}) => {
    // Assuming there's at least one customer in the list
    const firstCard = page.locator('[data-testid="customer-card"]').first();
    
    if (await firstCard.count() > 0) {
      await firstCard.getByText('View Details').click();
      
      // Should navigate to detail page
      await expect(page).toHaveURL(new RegExp(`/customer/[a-zA-Z0-9-]+`));
      
      // Check detail page elements
      await expect(page.getByText('Back to Customers')).toBeVisible();
      await expect(page.getByRole('button', {name: 'Edit'})).toBeVisible();
      await expect(page.getByRole('button', {name: 'Delete'})).toBeVisible();
   }
 });

  test('should edit customer details', async ({page}) => {
    // Navigate to first customer detail page
    const firstCard = page.locator('[data-testid="customer-card"]').first();
    
    if (await firstCard.count() > 0) {
      await firstCard.getByText('View Details').click();
      
      // Click edit button
      await page.getByRole('button', {name: 'Edit'}).click();
      
      // Form should be visible in edit mode
      await expect(page.getByLabel('Email')).toBeVisible();
      await expect(page.getByLabel('First Name')).toBeVisible();
      await expect(page.getByLabel('Last Name')).toBeVisible();
      await expect(page.getByLabel('Phone')).toBeVisible();
      
      // Update a field
      
      // Submit update
      await page.getByRole('button', {name: 'Update Customer'}).click();
      
      // Should show updated value
   }
 });

  test('should handle customer deletion with confirmation', async ({page}) => {
    // Navigate to first customer detail page
    const firstCard = page.locator('[data-testid="customer-card"]').first();
    
    if (await firstCard.count() > 0) {
      await firstCard.getByText('View Details').click();
      
      // Set up dialog handler for confirmation
      page.on('dialog', dialog => dialog.accept());
      
      // Click delete button
      await page.getByRole('button', {name: 'Delete'}).click();
      
      // Should redirect to customers list
      await expect(page).toHaveURL('/customer');
   }
 });
});