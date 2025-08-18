import type { Meta, StoryObj } from '@storybook/react';
import { QueryClient, QueryClientProvider } from '@tanstack/react-query';
import { CustomerForm } from '../../../../apps/web/components/CustomerForm';
import { CustomerCard } from '../../../../apps/web/components/CustomerCard';

// Create a mock query client for Storybook
const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      retry: false,
    },
  },
});

const meta: Meta<typeof CustomerForm> = {
  title: 'Components/Customer',
  component: CustomerForm,
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
const mockCustomer = {
  id: "Sample id",
  email: "Sample email",
  firstName: "Sample firstName",
  lastName: "Sample lastName",
  phone: "Sample phone",
  createdAt: "2024-01-01T00:00:00.000Z",
};

export const Form: Story = {
  args: {
    onSubmit: (data) => console.log('Form submitted:', data),
    isLoading: false,
  },
};

export const FormWithInitialData: Story = {
  args: {
    initialData: mockCustomer,
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
    error: 'Failed to save customer. Please try again.',
    isLoading: false,
  },
};

// Card Stories
const CardMeta: Meta<typeof CustomerCard> = {
  title: 'Components/CustomerCard',
  component: CustomerCard,
  decorators: [
    (Story) => (
      <div className="max-w-sm mx-auto p-6">
        <Story />
      </div>
    ),
  ],
};

export const Card: StoryObj<typeof CustomerCard> = {
  args: {
    customer: mockCustomer,
    showActions: true,
    onDelete: (id) => console.log('Delete customer:', id),
  },
};

export const CardWithoutActions: StoryObj<typeof CustomerCard> = {
  args: {
    customer: mockCustomer,
    showActions: false,
  },
};

// Multiple cards grid
export const CardGrid: StoryObj = {
  render: () => (
    <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6 p-6">
      {[...Array(6)].map((_, i) => (
        <CustomerCard 
          key={i}
          customer={ {
            ...mockCustomer,
            id: `customer-${i + 1}`,
          } }
          onDelete={(id) => console.log('Delete:', id)}
        />
      ))}
    </div>
  ),
};