'use client';

import Link from 'next/link';
import { Button } from '@ae-framework/ui/components/button';
import { Badge } from '@ae-framework/ui/components/badge';

interface Customer {
  id: string;
  email: string;
  firstName: string;
  lastName: string;
  phone: string;
  createdAt: string;
}

interface CustomerCardProps {
  customer: Customer;
  onDelete?: (id: string) => void;
  showActions?: boolean;
}

export function CustomerCard({ 
  customer, 
  onDelete, 
  showActions = true 
}: CustomerCardProps) {
  return (
    <div className="bg-white border border-gray-200 rounded-lg p-6 hover:shadow-md transition-shadow">
      <div className="flex justify-between items-start mb-4">
        <div className="flex-1">
          <h3 className="text-lg font-semibold text-gray-900 mb-1">
            Customer #{ customer.id.slice(0, 8) }
          </h3>
        </div>
        
      </div>

      <div className="space-y-2 mb-4">
      </div>

      <div className="text-xs text-gray-400 mb-4">
        <div>Created At: {new Date(customer.createdAt).toLocaleDateString()}</div>
      </div>

      {showActions && (
        <div className="flex gap-2">
          <Link href={`/customer/${ customer.id }`}>
            <Button variant="outline" size="sm" className="flex-1">
              View Details
            </Button>
          </Link>
          
          {onDelete && (
            <Button 
              variant="destructive" 
              size="sm"
              onClick={() => onDelete( customer.id )}
            >
              Delete
            </Button>
          )}
        </div>
      )}
    </div>
  );
}

// Helper function for status badge variants
function getStatusVariant(status: string) {
  switch (status?.toLowerCase()) {
    case 'active':
    case 'confirmed':
    case 'delivered':
      return 'success';
    case 'pending':
    case 'shipped':
      return 'warning';
    case 'inactive':
    case 'cancelled':
      return 'destructive';
    default:
      return 'secondary';
  }
}