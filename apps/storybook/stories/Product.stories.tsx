import type { Meta, StoryObj } from '@storybook/react';
import { QueryClient, QueryClientProvider } from '@tanstack/react-query';
import { ProductForm } from '../../../../apps/web/components/ProductForm';
import { ProductCard } from '../../../../apps/web/components/ProductCard';

// Create a mock query client for Storybook
const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      retry: false,
    },
  },
});

const meta: Meta<typeof ProductForm> = {
  title: 'Components/Product',
  component: ProductForm,
  decorators: [
    (Story) => (
      <QueryClientProvider client={queryClient}>
        <div className="max-w-2xl mx-auto p-6">
          <Story />
        </div>
      </QueryClientProvider>
    ),
  ],
  parameters: {
    layout: 'fullscreen',
  },
};

export default meta;
type Story = StoryObj<typeof meta>;

// Mock data
const mockProduct = {
  id: "Sample id",
  name: "Sample name",
  description: "Sample description",
  price: 99.99,
  stock: 42,
  category: "electronics",
  active: true,
  createdAt: "2024-01-01T00:00:00.000Z",
  updatedAt: "2024-01-01T00:00:00.000Z",
};

export const Form: Story = {
  args: {
    onSubmit: (data) => console.log('Form submitted:', data),
    isLoading: false,
  },
};

export const FormWithInitialData: Story = {
  args: {
    initialData: mockProduct,
    onSubmit: (data) => console.log('Form updated:', data),
    isLoading: false,
  },
};

export const FormLoading: Story = {
  args: {
    onSubmit: (data) => console.log('Form submitted:', data),
    isLoading: true,
  },
};

export const FormWithError: Story = {
  args: {
    onSubmit: (data) => console.log('Form submitted:', data),
    error: 'Failed to save product. Please try again.',
    isLoading: false,
  },
};

// Card Stories
const CardMeta: Meta<typeof ProductCard> = {
  title: 'Components/ProductCard',
  component: ProductCard,
  decorators: [
    (Story) => (
      <div className="max-w-sm mx-auto p-6">
        <Story />
      </div>
    ),
  ],
};

export const Card: StoryObj<typeof ProductCard> = {
  args: {
    product: mockProduct,
    showActions: true,
    onDelete: (id) => console.log('Delete product:', id),
  },
};

export const CardWithoutActions: StoryObj<typeof ProductCard> = {
  args: {
    product: mockProduct,
    showActions: false,
  },
};

// Multiple cards grid
export const CardGrid: StoryObj = {
  render: () => (
    <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6 p-6">
      {[...Array(6)].map((_, i) => (
        <ProductCard 
          key={i}
          product={{
            ...mockProduct,
            id: `product-${i + 1}`,
            name: `Name ${i + 1}`,
          }}
          onDelete={(id) => console.log('Delete:', id)}
        />
      ))}
    </div>
  ),
};