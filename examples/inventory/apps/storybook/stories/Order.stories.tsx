import type { Meta, StoryObj } from '@storybook/react';
import { QueryClient, QueryClientProvider } from '@tanstack/react-query';
import { OrderForm } from '../../../../apps/web/components/OrderForm';
import { OrderCard } from '../../../../apps/web/components/OrderCard';

// Create a mock query client for Storybook
const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      retry: false,
    },
  },
});

const meta: Meta<typeof OrderForm> = {
  title: 'Components/Order',
  component: OrderForm,
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
const mockOrder = {
  id: "Sample id",
  orderNumber: "Sample orderNumber",
  customerId: "Sample customerId",
  customerEmail: "Sample customerEmail",
  status: "pending",
  items: [],
  subtotal: 42,
  taxAmount: 42,
  shippingAmount: 42,
  total: 42,
  shippingAddress: {},
  notes: "Sample notes",
  orderDate: "2024-01-01T00:00:00.000Z",
  shippedDate: "2024-01-01T00:00:00.000Z",
  deliveredDate: "2024-01-01T00:00:00.000Z",
};

export const Form: Story = {
  args: {
    onSubmit: (data) => console.log('Form submitted:', data),
    isLoading: false,
  },
};

export const FormWithInitialData: Story = {
  args: {
    initialData: mockOrder,
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
    error: 'Failed to save order. Please try again.',
    isLoading: false,
  },
};

// Card Stories
const CardMeta: Meta<typeof OrderCard> = {
  title: 'Components/OrderCard',
  component: OrderCard,
  decorators: [
    (Story) => (
      <div className="max-w-sm mx-auto p-6">
        <Story />
      </div>
    ),
  ],
};

export const Card: StoryObj<typeof OrderCard> = {
  args: {
    order: mockOrder,
    showActions: true,
    onDelete: (id) => console.log('Delete order:', id),
  },
};

export const CardWithoutActions: StoryObj<typeof OrderCard> = {
  args: {
    order: mockOrder,
    showActions: false,
  },
};

// Multiple cards grid
export const CardGrid: StoryObj = {
  render: () => (
    <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6 p-6">
      {[...Array(6)].map((_, i) => (
        <OrderCard 
          key={i}
          order={
            ...mockOrder,
            id: `order-${i + 1}`,
          }
          onDelete={(id) => console.log('Delete:', id)}
        />
      ))}
    </div>
  ),
};