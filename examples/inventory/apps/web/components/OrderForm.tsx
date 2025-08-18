'use client';

import { useForm } from 'react-hook-form';
import { zodResolver } from '@hookform/resolvers/zod';
import { z } from 'zod';
import { Button } from '@ae-framework/ui/components/button';
import { Input } from '@ae-framework/ui/components/input';
import { Textarea } from '@ae-framework/ui/components/textarea';
import { Checkbox } from '@ae-framework/ui/components/checkbox';
import { Select, SelectContent, SelectItem, SelectTrigger, SelectValue } from '@ae-framework/ui/components/select';

// Zod schema for Order validation
const orderSchema = z.object({
  orderNumber: z.string(),
  customerId: z.string(),
  customerEmail: z.string(),
  status: z.enum(["pending"]),
  items: z.array(z.any()).min(1),
  subtotal: z.number().min(0),
  taxAmount: z.number().min(0),
  shippingAmount: z.number().min(0),
  total: z.number().min(0),
  shippingAddress: z.any(),
  notes: z.string().max(1000).optional(),
  orderDate: z.string().datetime(),
  shippedDate: z.string().datetime().optional(),
  deliveredDate: z.string().datetime().optional(),
});

type OrderFormData = z.infer<typeof orderSchema>;

interface OrderFormProps {
  initialData?: Partial<OrderFormData>;
  onSubmit: (data: OrderFormData) => void;
  onCancel?: () => void;
  isLoading?: boolean;
  error?: string;
}

export function OrderForm({ 
  initialData, 
  onSubmit, 
  onCancel, 
  isLoading = false,
  error 
}: OrderFormProps) {
  const {
    register,
    handleSubmit,
    formState: { errors },
    setValue,
    watch
  } = useForm<OrderFormData>({
    resolver: zodResolver(orderSchema),
    defaultValues: initialData
  });

  return (
    <form onSubmit={handleSubmit(onSubmit)} className="space-y-6">
      {error && (
        <div className="bg-red-50 border border-red-200 rounded-md p-3">
          <p className="text-red-800 text-sm">{error}</p>
        </div>
      )}

      <div>
        <label htmlFor="orderNumber" className="block text-sm font-medium text-gray-700 mb-1">
          Order Number *
        </label>
        <Textarea
          id="orderNumber"
          placeholder="Customer order entity with comprehensive order management"
          {...register('orderNumber')}
          className={ errors.orderNumber ? 'border-red-500' : '' }
        />
        { errors.orderNumber && (
          <p className="text-red-600 text-sm mt-1">
            { errors.orderNumber?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="customerId" className="block text-sm font-medium text-gray-700 mb-1">
          Customer Id *
        </label>
        <Textarea
          id="customerId"
          placeholder="Customer order entity with comprehensive order management"
          {...register('customerId')}
          className={ errors.customerId ? 'border-red-500' : '' }
        />
        { errors.customerId && (
          <p className="text-red-600 text-sm mt-1">
            { errors.customerId?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="customerEmail" className="block text-sm font-medium text-gray-700 mb-1">
          Customer Email *
        </label>
        <Textarea
          id="customerEmail"
          placeholder="Customer order entity with comprehensive order management"
          {...register('customerEmail')}
          className={ errors.customerEmail ? 'border-red-500' : '' }
        />
        { errors.customerEmail && (
          <p className="text-red-600 text-sm mt-1">
            { errors.customerEmail?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="status" className="block text-sm font-medium text-gray-700 mb-1">
          Status *
        </label>
        <Textarea
          id="status"
          placeholder="Customer order entity with comprehensive order management"
          {...register('status')}
          className={ errors.status ? 'border-red-500' : '' }
        />
        { errors.status && (
          <p className="text-red-600 text-sm mt-1">
            { errors.status?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="items" className="block text-sm font-medium text-gray-700 mb-1">
          Items *
        </label>
        <Input
          id="items"
          type="text"
          placeholder="Customer order entity with comprehensive order management"
          {...register('items')}
          className={ errors.items ? 'border-red-500' : '' }
        />
                { errors.items && (
          <p className="text-red-600 text-sm mt-1">
            { errors.items?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="subtotal" className="block text-sm font-medium text-gray-700 mb-1">
          Subtotal *
        </label>
        <Input
          id="subtotal"
          type="number"
          placeholder="Customer order entity with comprehensive order management"
          {...register('subtotal', { valueAsNumber: true })}
          className={ errors.subtotal ? 'border-red-500' : '' }
        />
                { errors.subtotal && (
          <p className="text-red-600 text-sm mt-1">
            { errors.subtotal?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="taxAmount" className="block text-sm font-medium text-gray-700 mb-1">
          Tax Amount *
        </label>
        <Input
          id="taxAmount"
          type="number"
          placeholder="Customer order entity with comprehensive order management"
          {...register('taxAmount', { valueAsNumber: true })}
          className={ errors.taxAmount ? 'border-red-500' : '' }
        />
                { errors.taxAmount && (
          <p className="text-red-600 text-sm mt-1">
            { errors.taxAmount?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="shippingAmount" className="block text-sm font-medium text-gray-700 mb-1">
          Shipping Amount *
        </label>
        <Input
          id="shippingAmount"
          type="number"
          placeholder="Customer order entity with comprehensive order management"
          {...register('shippingAmount', { valueAsNumber: true })}
          className={ errors.shippingAmount ? 'border-red-500' : '' }
        />
                { errors.shippingAmount && (
          <p className="text-red-600 text-sm mt-1">
            { errors.shippingAmount?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="total" className="block text-sm font-medium text-gray-700 mb-1">
          Total *
        </label>
        <Input
          id="total"
          type="number"
          placeholder="Customer order entity with comprehensive order management"
          {...register('total', { valueAsNumber: true })}
          className={ errors.total ? 'border-red-500' : '' }
        />
                { errors.total && (
          <p className="text-red-600 text-sm mt-1">
            { errors.total?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="shippingAddress" className="block text-sm font-medium text-gray-700 mb-1">
          Shipping Address *
        </label>
        <Input
          id="shippingAddress"
          type="text"
          placeholder="Customer order entity with comprehensive order management"
          {...register('shippingAddress')}
          className={ errors.shippingAddress ? 'border-red-500' : '' }
        />
                { errors.shippingAddress && (
          <p className="text-red-600 text-sm mt-1">
            { errors.shippingAddress?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="notes" className="block text-sm font-medium text-gray-700 mb-1">
          Notes
        </label>
        <Textarea
          id="notes"
          placeholder="Customer order entity with comprehensive order management"
          {...register('notes')}
          className={ errors.notes ? 'border-red-500' : '' }
        />
        { errors.notes && (
          <p className="text-red-600 text-sm mt-1">
            { errors.notes?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="orderDate" className="block text-sm font-medium text-gray-700 mb-1">
          Order Date *
        </label>
        <Input
          id="orderDate"
          type="datetime-local"
          placeholder="Customer order entity with comprehensive order management"
          {...register('orderDate')}
          className={ errors.orderDate ? 'border-red-500' : '' }
        />
                { errors.orderDate && (
          <p className="text-red-600 text-sm mt-1">
            { errors.orderDate?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="shippedDate" className="block text-sm font-medium text-gray-700 mb-1">
          Shipped Date
        </label>
        <Input
          id="shippedDate"
          type="datetime-local"
          placeholder="Customer order entity with comprehensive order management"
          {...register('shippedDate')}
          className={ errors.shippedDate ? 'border-red-500' : '' }
        />
                { errors.shippedDate && (
          <p className="text-red-600 text-sm mt-1">
            { errors.shippedDate?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="deliveredDate" className="block text-sm font-medium text-gray-700 mb-1">
          Delivered Date
        </label>
        <Input
          id="deliveredDate"
          type="datetime-local"
          placeholder="Customer order entity with comprehensive order management"
          {...register('deliveredDate')}
          className={ errors.deliveredDate ? 'border-red-500' : '' }
        />
                { errors.deliveredDate && (
          <p className="text-red-600 text-sm mt-1">
            { errors.deliveredDate?.message }
          </p>
        ) }
      </div>

      <div className="flex gap-3 pt-4">
        <Button 
          type="submit" 
          disabled={isLoading}
          className="flex-1"
        >
          {isLoading ? 'Saving...' : initialData ? 'Update Order' : 'Create Order'}
        </Button>
        
        {onCancel && (
          <Button 
            type="button" 
            variant="outline"
            onClick={onCancel}
            disabled={isLoading}
          >
            Cancel
          </Button>
        ) }
      </div>
    </form>
  );
}