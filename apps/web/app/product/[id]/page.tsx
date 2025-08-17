'use client';

import { useState } from 'react';
import { useRouter } from 'next/navigation';
import { useQuery, useMutation, useQueryClient } from '@tanstack/react-query';
import { Button } from '@ae-framework/ui/components/button';
import { ProductForm } from '../../../components/ProductForm';
import Link from 'next/link';

interface Product {
  id: string;
  name: string;
  description: string;
  price: number;
  stock: number;
  category: string;
  active: boolean;
  createdAt: string;
  updatedAt: string;
}

interface ProductUpdateData {
  name: string;
  description?: string;
  price: number;
  stock: number;
  category: string;
  active: boolean;
}

export default function ProductDetailPage({ 
  params 
}: { 
  params: { id: string } 
}) {
  const router = useRouter();
  const queryClient = useQueryClient();
  const [isEditing, setIsEditing] = useState(false);

  const { data: product, isLoading, error } = useQuery({
    queryKey: ['product', params.id],
    queryFn: async () => {
      const response = await fetch(`/api/products/${params.id}`);
      if (!response.ok) throw new Error('Failed to fetch product');
      return response.json();
    }
  });

  const updateMutation = useMutation({
    mutationFn: async (data: ProductUpdateData) => {
      const response = await fetch(`/api/products/${params.id}`, {
        method: 'PUT',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(data)
      });
      
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.message || 'Failed to update product');
      }
      
      return response.json();
    },
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ['product', params.id] });
      queryClient.invalidateQueries({ queryKey: ['products'] });
      setIsEditing(false);
    }
  });

  const deleteMutation = useMutation({
    mutationFn: async () => {
      const response = await fetch(`/api/products/${params.id}`, {
        method: 'DELETE'
      });
      
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.message || 'Failed to delete product');
      }
    },
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ['products'] });
      router.push('/product');
    }
  });

  const handleUpdate = (data: ProductUpdateData) => {
    updateMutation.mutate(data);
  };

  const handleDelete = () => {
    if (confirm('Are you sure you want to delete this product? This action cannot be undone.')) {
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

  if (error || !product) {
    return (
      <div className="p-6 max-w-2xl mx-auto">
        <div className="bg-red-50 border border-red-200 rounded-md p-4">
          <h3 className="text-red-800 font-medium">Error loading product</h3>
          <p className="text-red-600">{error?.message || 'Product not found'}</p>
        </div>
      </div>
    );
  }

  return (
    <div className="p-6 max-w-2xl mx-auto">
      <div className="mb-6">
        <div className="flex items-center justify-between mb-4">
          <Link href="/product">
            <Button variant="outline">← Back to Products</Button>
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
          { product.name }
        </h1>
      </div>

      <div className="bg-white border rounded-lg p-6">
        {isEditing ? (
          <div>
            <div className="mb-4">
              <h2 className="text-lg font-medium">Edit Product</h2>
            </div>
            <ProductForm
              initialData={ product }
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
                Name
              </label>
              <div className="text-gray-900">
                { {product.name} }
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Description
              </label>
              <div className="text-gray-900">
                { {product.description} }
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Price
              </label>
              <div className="text-gray-900">
                { {product.price} }
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Stock
              </label>
              <div className="text-gray-900">
                { {product.stock} }
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Category
              </label>
              <div className="text-gray-900">
                { {product.category} }
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Active
              </label>
              <div className="text-gray-900">
                { {product.active} }
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Created At
              </label>
              <div className="text-gray-900">
                { {product.createdAt} }
              </div>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Updated At
              </label>
              <div className="text-gray-900">
                { {product.updatedAt} }
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