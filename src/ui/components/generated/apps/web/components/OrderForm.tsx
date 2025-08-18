'use client';

import {useForm} from 'react-hook-form';
import {zodResolver} from '@hookform/resolvers/zod';
import {z} from 'zod';
import {Button} from '@ae-framework/ui/components/button';
import {Input} from '@ae-framework/ui/components/input';
import {Textarea} from '@ae-framework/ui/components/textarea';
import {Checkbox} from '@ae-framework/ui/components/checkbox';
import {Select, SelectContent, SelectItem, SelectTrigger, SelectValue} from '@ae-framework/ui/components/select';

// Zod schema for Order validation
const orderSchema = z.object({
  customerId: z.string(),
  status: z.enum(["pending"]),
  total: z.number().min(0),
  items: z.array(z.any()).min(1),
  shippingAddress: z.any(),
  orderDate: z.string().datetime(),
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
    formState: {errors},
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
        <label htmlFor="customerId" className="block text-sm font-medium text-gray-700 mb-1">
          Customer Id *
        </label>
        <Textarea
          id="customerId"
          placeholder="Customer order entity"
          {...register('customerId')}
          className={errors.customerId ? 'border-red-500' : ''}
        />
        {errors.customerId && (
          <p className="text-red-600 text-sm mt-1">
            {errors.customerId?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="status" className="block text-sm font-medium text-gray-700 mb-1">
          Status *
        </label>
        <Textarea
          id="status"
          placeholder="Customer order entity"
          {...register('status')}
          className={errors.status ? 'border-red-500' : ''}
        />
        {errors.status && (
          <p className="text-red-600 text-sm mt-1">
            {errors.status?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="total" className="block text-sm font-medium text-gray-700 mb-1">
          Total *
        </label>
        <Input
          id="total"
          type="number"
          placeholder="Customer order entity"
          {...register('total', {valueAsNumber: true})}
          className={errors.total ? 'border-red-500' : ''}
        />
                {errors.total && (
          <p className="text-red-600 text-sm mt-1">
            {errors.total?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="items" className="block text-sm font-medium text-gray-700 mb-1">
          Items *
        </label>
        <Input
          id="items"
          type="text"
          placeholder="Customer order entity"
          {...register('items')}
          className={errors.items ? 'border-red-500' : ''}
        />
                {errors.items && (
          <p className="text-red-600 text-sm mt-1">
            {errors.items?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="shippingAddress" className="block text-sm font-medium text-gray-700 mb-1">
          Shipping Address *
        </label>
        <Input
          id="shippingAddress"
          type="text"
          placeholder="Customer order entity"
          {...register('shippingAddress')}
          className={errors.shippingAddress ? 'border-red-500' : ''}
        />
                {errors.shippingAddress && (
          <p className="text-red-600 text-sm mt-1">
            {errors.shippingAddress?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="orderDate" className="block text-sm font-medium text-gray-700 mb-1">
          Order Date *
        </label>
        <Input
          id="orderDate"
          type="datetime-local"
          placeholder="Customer order entity"
          {...register('orderDate')}
          className={errors.orderDate ? 'border-red-500' : ''}
        />
                {errors.orderDate && (
          <p className="text-red-600 text-sm mt-1">
            {errors.orderDate?.message}
          </p>
        )}
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
        )}
      </div>
    </form>
  );
}