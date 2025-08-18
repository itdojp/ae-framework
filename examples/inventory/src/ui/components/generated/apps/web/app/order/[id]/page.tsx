'use client';

import {useState} from 'react';
import {useRouter} from 'next/navigation';
import {useQuery, useMutation, useQueryClient} from '@tanstack/react-query';
import {Button} from '@ae-framework/ui/components/button';
import {OrderForm} from '../../../components/OrderForm';
import Link from 'next/link';

interface Order {
  id: string;
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
  notes: string;
  orderDate: string;
  shippedDate: string;
  deliveredDate: string;
}

interface OrderUpdateData {
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

export default function OrderDetailPage({
  params 
}: {
  params: {id: string} 
}) {
  const router = useRouter();
  const queryClient = useQueryClient();
  const [isEditing, setIsEditing] = useState(false);

  const {data: order, isLoading, error} = useQuery({
    queryKey: ['order', params.id],
    queryFn: async () => {
      const response = await fetch(`/api/orders/${params.id}`);
      if (!response.ok) throw new Error('Failed to fetch order');
      return response.json();
   }
 });

  const updateMutation = useMutation({
    mutationFn: async (data: OrderUpdateData) => {
      const response = await fetch(`/api/orders/${params.id}`, {
        method: 'PUT',
        headers: {'Content-Type': 'application/json'},
        body: JSON.stringify(data)
     });
      
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.message || 'Failed to update order');
     }
      
      return response.json();
   },
    onSuccess: () => {
      queryClient.invalidateQueries({queryKey: ['order', params.id]});
      queryClient.invalidateQueries({queryKey: ['orders']});
      setIsEditing(false);
   }
 });

  const deleteMutation = useMutation({
    mutationFn: async () => {
      const response = await fetch(`/api/orders/${params.id}`, {
        method: 'DELETE'
     });
      
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.message || 'Failed to delete order');
     }
   },
    onSuccess: () => {
      queryClient.invalidateQueries({queryKey: ['orders']});
      router.push('/order');
   }
 });

  const handleUpdate = (data: OrderUpdateData) => {
    updateMutation.mutate(data);
 };

  const handleDelete = () => {
    if (confirm('Are you sure you want to delete this order? This action cannot be undone.')) {
      deleteMutation.mutate();
   }
 };

  if (isLoading) {
    return (
      <div className="p-6 max-w-2xl mx-auto">
        <div className="animate-pulse">
          <div className="h-8 bg-gray-200 rounded mb-4"></div>
          <div className="h-64 bg-gray-200 rounded"></div>
        </div>
      </div>
    );
 }

  if (error || !order) {
    return (
      <div className="p-6 max-w-2xl mx-auto">
        <div className="bg-red-50 border border-red-200 rounded-md p-4">
          <h3 className="text-red-800 font-medium">Error loading order</h3>
          <p className="text-red-600">{error?.message || 'Order not found'}</p>
        </div>
      </div>
    );
 }

  return (
    <div className="p-6 max-w-2xl mx-auto">
      <div className="mb-6">
        <div className="flex items-center justify-between mb-4">
          <Link href="/order">
            <Button variant="outline">← Back to Orders</Button>
          </Link>
          
          <div className="flex gap-2">
            {!isEditing && (
              <Button onClick={() => setIsEditing(true)}>
                Edit
              </Button>
            )}
            <Button 
              variant="destructive" 
              onClick={handleDelete}
              disabled={deleteMutation.isPending}
            >
              {deleteMutation.isPending ? 'Deleting...' : 'Delete'}
            </Button>
          </div>
        </div>
        
        <h1 className="text-3xl font-bold text-gray-900">
          Order Details
        </h1>
      </div>

      <div className="bg-white border rounded-lg p-6">
        {isEditing ? (
          <div>
            <div className="mb-4">
              <h2 className="text-lg font-medium">Edit Order</h2>
            </div>
            <OrderForm
              initialData={order}
              onSubmit={handleUpdate}
              isLoading={updateMutation.isPending}
              error={updateMutation.error?.message}
              onCancel={() => setIsEditing(false)}
            />
          </div>
        ) : (
          <div className="space-y-4">
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Order Number
              </label>
              <div className="text-gray-900">
                {order.orderNumber}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Customer Id
              </label>
              <div className="text-gray-900">
                {order.customerId}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Customer Email
              </label>
              <div className="text-gray-900">
                {order.customerEmail}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Status
              </label>
              <div className="text-gray-900">
                {order.status}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Items
              </label>
              <div className="text-gray-900">
                {order.items}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Subtotal
              </label>
              <div className="text-gray-900">
                {order.subtotal}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Tax Amount
              </label>
              <div className="text-gray-900">
                {order.taxAmount}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Shipping Amount
              </label>
              <div className="text-gray-900">
                {order.shippingAmount}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Total
              </label>
              <div className="text-gray-900">
                {order.total}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Shipping Address
              </label>
              <div className="text-gray-900">
                {order.shippingAddress}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Notes
              </label>
              <div className="text-gray-900">
                {order.notes}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Order Date
              </label>
              <div className="text-gray-900">
                {order.orderDate}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Shipped Date
              </label>
              <div className="text-gray-900">
                {order.shippedDate}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Delivered Date
              </label>
              <div className="text-gray-900">
                {order.deliveredDate}
              </div>
            </div>
          </div>
        )}
      </div>

      {(updateMutation.error || deleteMutation.error) && (
        <div className="mt-4 bg-red-50 border border-red-200 rounded-md p-4">
          <h3 className="text-red-800 font-medium">Error</h3>
          <p className="text-red-600">
            {updateMutation.error?.message || deleteMutation.error?.message}
          </p>
        </div>
      )}
    </div>
  );
}