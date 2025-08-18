'use client';

import { useState } from 'react';
import { useQuery } from '@tanstack/react-query';
import Link from 'next/link';
import { Button } from '@ae-framework/ui/components/button';
import { Input } from '@ae-framework/ui/components/input';
import { CustomerCard } from '../../../components/CustomerCard';

interface Customer {
  id: string;
  email: string;
  firstName: string;
  lastName: string;
  phone: string;
  createdAt: string;
}

export default function CustomerListPage() {
  const [search, setSearch] = useState('');
  const [filter, setFilter] = useState('all');

  const { data: customers, isLoading, error } = useQuery({
    queryKey: ['customers', search, filter],
    queryFn: async () => {
      const params = new URLSearchParams();
      if (search) params.set('search', search);
      if (filter !== 'all') params.set('filter', filter);
      
      const response = await fetch(`/api/customers?${params}`);
      if (!response.ok) throw new Error('Failed to fetch customers');
      return response.json();
    }
  });

  if (error) {
    return (
      <div className="p-6">
        <div className="bg-red-50 border border-red-200 rounded-md p-4">
          <h3 className="text-red-800 font-medium">Error loading customers</h3>
          <p className="text-red-600">{error.message}</p>
        </div>
      </div>
    );
  }

  return (
    <div className="p-6 max-w-7xl mx-auto">
      <div className="mb-6">
        <div className="flex justify-between items-center mb-4">
          <h1 className="text-3xl font-bold text-gray-900">Customers</h1>
          <Link href="/customer/new">
            <Button>Add New Customer</Button>
          </Link>
        </div>

        <div className="flex gap-4 mb-4">
          <Input
            placeholder="Search customers..."
            value={search}
            onChange={(e) => setSearch(e.target.value)}
            className="max-w-sm"
          />
          
          <select
            value={filter}
            onChange={(e) => setFilter(e.target.value)}
            className="border rounded-md px-3 py-2"
          >
            <option value="all">All Customers</option>
          </select>
        </div>
      </div>

      {isLoading ? (
        <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
          {[...Array(6)].map((_, i) => (
            <div key={i} className="bg-white border rounded-lg p-6 animate-pulse">
              <div className="h-4 bg-gray-200 rounded mb-2"></div>
              <div className="h-4 bg-gray-200 rounded w-3/4 mb-4"></div>
              <div className="h-8 bg-gray-200 rounded"></div>
            </div>
          ))}
        </div>
      ) : (
        <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
          { customers?.map((customer: Customer) => (
            <CustomerCard key={ customer.id} customer={ customer } />
          )) }
        </div>
      )}

      { customers?.length === 0 && !isLoading && (
        <div className="text-center py-12">
          <h3 className="text-lg font-medium text-gray-900 mb-2">
            No customers found
          </h3>
          <p className="text-gray-500 mb-4">
            Get started by creating your first customer.
          </p>
          <Link href="/customer/new">
            <Button>Add New Customer</Button>
          </Link>
        </div>
      )}
    </div>
  );
}