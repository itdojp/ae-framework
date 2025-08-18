'use client';

import Link from 'next/link';
import { Button } from '@ae-framework/ui/components/button';
import { Badge } from '@ae-framework/ui/components/badge';

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

interface ProductCardProps {
  product: Product;
  onDelete?: (id: string) => void;
  showActions?: boolean;
}

export function ProductCard({ 
  product, 
  onDelete, 
  showActions = true 
}: ProductCardProps) {
  return (
    <div className="bg-white border border-gray-200 rounded-lg p-6 hover:shadow-md transition-shadow">
      <div className="flex justify-between items-start mb-4">
        <div className="flex-1">
          <h3 className="text-lg font-semibold text-gray-900 mb-1">
            { product.name }
          </h3>
          <p className="text-gray-600 text-sm line-clamp-2">
            { product.description }
          </p>
        </div>
        
        <Badge variant={getStatusVariant(product.active)}>
          { product.active }
        </Badge>
      </div>

      <div className="space-y-2 mb-4">
        <div className="flex justify-between text-sm">
          <span className="text-gray-500">Price:</span>
          <span className="text-gray-900 font-medium">
            ${product.price}
          </span>
        </div>
        <div className="flex justify-between text-sm">
          <span className="text-gray-500">Category:</span>
          <span className="text-gray-900 font-medium">
            {new Date(product.category).toLocaleDateString()}
          </span>
        </div>
        <div className="flex justify-between text-sm">
          <span className="text-gray-500">Stock:</span>
          <span className="text-gray-900 font-medium">
            {product.stock}
          </span>
        </div>
      </div>

      <div className="text-xs text-gray-400 mb-4">
        <div>Created At: {new Date(product.createdAt).toLocaleDateString()}</div>
        <div>Updated At: {new Date(product.updatedAt).toLocaleDateString()}</div>
      </div>

      {showActions && (
        <div className="flex gap-2">
          <Link href={`/product/${ product.id }`}>
            <Button variant="outline" size="sm" className="flex-1">
              View Details
            </Button>
          </Link>
          
          {onDelete && (
            <Button 
              variant="destructive" 
              size="sm"
              onClick={() => onDelete( product.id )}
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