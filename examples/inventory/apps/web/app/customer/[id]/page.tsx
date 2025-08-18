'use client';

import { useState } from 'react';
import { useRouter } from 'next/navigation';
import { useQuery, useMutation, useQueryClient } from '@tanstack/react-query';
import { Button } from '@ae-framework/ui/components/button';
import { CustomerForm } from '../../../components/CustomerForm';
import Link from 'next/link';

interface Customer {
  id: string;
  email: string;
  firstName: string;
  lastName: string;
  phone: string;
  createdAt: string;
}

interface CustomerUpdateData {
  email: string;
  firstName: string;
  lastName: string;
  phone?: string;
}

export default function CustomerDetailPage({ 
  params 
}: { 
  params: { id: string } 
}) {
  const router = useRouter();
  const queryClient = useQueryClient();
  const [isEditing, setIsEditing] = useState(false);

  const { data: customer, isLoading, error } = useQuery({
    queryKey: ['customer', params.id],
    queryFn: async () => {
      const response = await fetch(`/api/customers/${params.id}`);
      if (!response.ok) throw new Error('Failed to fetch customer');
      return response.json();
    }
  });

  const updateMutation = useMutation({
    mutationFn: async (data: CustomerUpdateData) => {
      const response = await fetch(`/api/customers/${params.id}`, {
        method: 'PUT',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(data)
      });
      
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.message || 'Failed to update customer');
      }
      
      return response.json();
    },
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ['customer', params.id] });
      queryClient.invalidateQueries({ queryKey: ['customers'] });
      setIsEditing(false);
    }
  });

  const deleteMutation = useMutation({
    mutationFn: async () => {
      const response = await fetch(`/api/customers/${params.id}`, {
        method: 'DELETE'
      });
      
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.message || 'Failed to delete customer');
      }
    },
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ['customers'] });
      router.push('/customer');
    }
  });

  const handleUpdate = (data: CustomerUpdateData) => {
    updateMutation.mutate(data);
  };

  const handleDelete = () => {
    if (confirm('Are you sure you want to delete this customer? This action cannot be undone.')) {
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

  if (error || !customer) {
    return (
      <div className="p-6 max-w-2xl mx-auto">
        <div className="bg-red-50 border border-red-200 rounded-md p-4">
          <h3 className="text-red-800 font-medium">Error loading customer</h3>
          <p className="text-red-600">{error?.message || 'Customer not found'}</p>
        </div>
      </div>
    );
  }

  return (
    <div className="p-6 max-w-2xl mx-auto">
      <div className="mb-6">
        <div className="flex items-center justify-between mb-4">
          <Link href="/customer">
            <Button variant="outline">← Back to Customers</Button>
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
          Customer Details
        </h1>
      </div>

      <div className="bg-white border rounded-lg p-6">
        {isEditing ? (
          <div>
            <div className="mb-4">
              <h2 className="text-lg font-medium">Edit Customer</h2>
            </div>
            <CustomerForm
              initialData={ customer }
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
                Email
              </label>
              <div className="text-gray-900">
                {customer.email}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                First Name
              </label>
              <div className="text-gray-900">
                {customer.firstName}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Last Name
              </label>
              <div className="text-gray-900">
                {customer.lastName}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Phone
              </label>
              <div className="text-gray-900">
                {customer.phone}
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Created At
              </label>
              <div className="text-gray-900">
                {customer.createdAt}
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