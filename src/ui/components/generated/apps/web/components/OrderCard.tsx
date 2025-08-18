'use client';

import Link from 'next/link';
import {Button} from '@ae-framework/ui/components/button';
import {Badge} from '@ae-framework/ui/components/badge';

interface Order {
  id: string;
  customerId: string;
  status: string;
  total: number;
  items: any[];
  shippingAddress: any;
  orderDate: string;
}

interface OrderCardProps {
  order: Order;
  onDelete?: (id: string) => void;
  showActions?: boolean;
}

export function OrderCard({
  order, 
  onDelete, 
  showActions = true 
}: OrderCardProps) {
  return (
    <div className="bg-white border border-gray-200 rounded-lg p-6 hover:shadow-md transition-shadow">
      <div className="flex justify-between items-start mb-4">
        <div className="flex-1">
          <h3 className="text-lg font-semibold text-gray-900 mb-1">
            Order #{order.id.slice(0, 8)}
          </h3>
        </div>
        
        <Badge variant={getStatusVariant(order.status)}>
          {order.status}
        </Badge>
      </div>

      <div className="space-y-2 mb-4">
        <div className="flex justify-between text-sm">
          <span className="text-gray-500">Status:</span>
          <span className="text-gray-900 font-medium">
            {new Date(order.status).toLocaleDateString()}
          </span>
        </div>
        <div className="flex justify-between text-sm">
          <span className="text-gray-500">Total:</span>
          <span className="text-gray-900 font-medium">
            ${order.total}
          </span>
        </div>
      </div>

      <div className="text-xs text-gray-400 mb-4">
        <div>Order Date: {new Date(order.orderDate).toLocaleDateString()}</div>
      </div>

      {showActions && (
        <div className="flex gap-2">
          <Link href={`/order/${order.id}`}>
            <Button variant="outline" size="sm" className="flex-1">
              View Details
            </Button>
          </Link>
          
          {onDelete && (
            <Button 
              variant="destructive" 
              size="sm"
              onClick={() => onDelete( order.id )}
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