'use client';

import {useRouter} from 'next/navigation';
import {useMutation, useQueryClient} from '@tanstack/react-query';
import {OrderForm} from '../../../components/OrderForm';
import {Button} from '@ae-framework/ui/components/button';
import Link from 'next/link';

interface OrderCreateData {
  orderNumber: string;
  customerId: string;
  customerEmail: string;
  status: string;
  items: any[];
  subtotal: number;
  taxAmount: number;
  shippingAmount: number;
  total: number;
  shippingAddress: any;
  notes?: string;
  orderDate: string;
  shippedDate?: string;
  deliveredDate?: string;
}

export default function NewOrderPage() {
  const router = useRouter();
  const queryClient = useQueryClient();

  const createMutation = useMutation({
    mutationFn: async (data: OrderCreateData) => {
      const response = await fetch('/api/orders', {
        method: 'POST',
        headers: {'Content-Type': 'application/json'},
        body: JSON.stringify(data)
     });
      
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.message || 'Failed to create order');
     }
      
      return response.json();
   },
    onSuccess: () => {
      queryClient.invalidateQueries({queryKey: ['orders']});
      router.push('/order');
   }
 });

  const handleSubmit = (data: OrderCreateData) => {
    createMutation.mutate(data);
 };

  return (
    <div className="p-6 max-w-2xl mx-auto">
      <div className="mb-6">
        <div className="flex items-center gap-4 mb-4">
          <Link href="/order">
            <Button variant="outline">← Back to Orders</Button>
          </Link>
        </div>
        <h1 className="text-3xl font-bold text-gray-900">Create New Order</h1>
        <p className="text-gray-600 mt-2">
          Fill in the details below to create a new order.
        </p>
      </div>

      <div className="bg-white border rounded-lg p-6">
        <OrderForm
          onSubmit={handleSubmit}
          isLoading={createMutation.isPending}
          error={createMutation.error?.message}
        />
      </div>

      {createMutation.error && (
        <div className="mt-4 bg-red-50 border border-red-200 rounded-md p-4">
          <h3 className="text-red-800 font-medium">Error creating order</h3>
          <p className="text-red-600">{createMutation.error.message}</p>
        </div>
      )}
    </div>
  );
}