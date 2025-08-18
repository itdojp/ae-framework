'use client';

import { useRouter } from 'next/navigation';
import { useMutation, useQueryClient } from '@tanstack/react-query';
import { ProductForm } from '../../../components/ProductForm';
import { Button } from '@ae-framework/ui/components/button';
import Link from 'next/link';

interface ProductCreateData {
  name: string;
  description?: string;
  price: number;
  stock: number;
  lowStockThreshold: number;
  category: string;
  sku: string;
  weight?: number;
  dimensions?: any;
  active: boolean;
  tags?: any[];
}

export default function NewProductPage() {
  const router = useRouter();
  const queryClient = useQueryClient();

  const createMutation = useMutation({
    mutationFn: async (data: ProductCreateData) => {
      const response = await fetch('/api/products', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(data)
      });
      
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.message || 'Failed to create product');
      }
      
      return response.json();
    },
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ['products'] });
      router.push('/product');
    }
  });

  const handleSubmit = (data: ProductCreateData) => {
    createMutation.mutate(data);
  };

  return (
    <div className="p-6 max-w-2xl mx-auto">
      <div className="mb-6">
        <div className="flex items-center gap-4 mb-4">
          <Link href="/product">
            <Button variant="outline">← Back to Products</Button>
          </Link>
        </div>
        <h1 className="text-3xl font-bold text-gray-900">Create New Product</h1>
        <p className="text-gray-600 mt-2">
          Fill in the details below to create a new product.
        </p>
      </div>

      <div className="bg-white border rounded-lg p-6">
        <ProductForm
          onSubmit={handleSubmit}
          isLoading={createMutation.isPending}
          error={createMutation.error?.message}
        />
      </div>

      {createMutation.error && (
        <div className="mt-4 bg-red-50 border border-red-200 rounded-md p-4">
          <h3 className="text-red-800 font-medium">Error creating product</h3>
          <p className="text-red-600">{createMutation.error.message}</p>
        </div>
      )}
    </div>
  );
}