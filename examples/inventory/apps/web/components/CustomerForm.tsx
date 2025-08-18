'use client';

import { useForm } from 'react-hook-form';
import { zodResolver } from '@hookform/resolvers/zod';
import { z } from 'zod';
import { Button } from '@ae-framework/ui/components/button';
import { Input } from '@ae-framework/ui/components/input';
import { Textarea } from '@ae-framework/ui/components/textarea';
import { Checkbox } from '@ae-framework/ui/components/checkbox';
import { Select, SelectContent, SelectItem, SelectTrigger, SelectValue } from '@ae-framework/ui/components/select';

// Zod schema for Customer validation
const customerSchema = z.object({
  email: z.string(),
  firstName: z.string().min(1).max(50),
  lastName: z.string().min(1).max(50),
  phone: z.string().optional(),
});

type CustomerFormData = z.infer<typeof customerSchema>;

interface CustomerFormProps {
  initialData?: Partial<CustomerFormData>;
  onSubmit: (data: CustomerFormData) => void;
  onCancel?: () => void;
  isLoading?: boolean;
  error?: string;
}

export function CustomerForm({ 
  initialData, 
  onSubmit, 
  onCancel, 
  isLoading = false,
  error 
}: CustomerFormProps) {
  const {
    register,
    handleSubmit,
    formState: { errors },
    setValue,
    watch
  } = useForm<CustomerFormData>({
    resolver: zodResolver(customerSchema),
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
        <label htmlFor="email" className="block text-sm font-medium text-gray-700 mb-1">
          Email *
        </label>
        <Textarea
          id="email"
          placeholder="Customer entity for order management"
          {...register('email')}
          className={ errors.email ? 'border-red-500' : '' }
        />
        { errors.email && (
          <p className="text-red-600 text-sm mt-1">
            { errors.email?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="firstName" className="block text-sm font-medium text-gray-700 mb-1">
          First Name *
        </label>
        <Textarea
          id="firstName"
          placeholder="Customer entity for order management"
          {...register('firstName')}
          className={ errors.firstName ? 'border-red-500' : '' }
        />
        { errors.firstName && (
          <p className="text-red-600 text-sm mt-1">
            { errors.firstName?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="lastName" className="block text-sm font-medium text-gray-700 mb-1">
          Last Name *
        </label>
        <Textarea
          id="lastName"
          placeholder="Customer entity for order management"
          {...register('lastName')}
          className={ errors.lastName ? 'border-red-500' : '' }
        />
        { errors.lastName && (
          <p className="text-red-600 text-sm mt-1">
            { errors.lastName?.message }
          </p>
        ) }
      </div>

      <div>
        <label htmlFor="phone" className="block text-sm font-medium text-gray-700 mb-1">
          Phone
        </label>
        <Textarea
          id="phone"
          placeholder="Customer entity for order management"
          {...register('phone')}
          className={ errors.phone ? 'border-red-500' : '' }
        />
        { errors.phone && (
          <p className="text-red-600 text-sm mt-1">
            { errors.phone?.message }
          </p>
        ) }
      </div>

      <div className="flex gap-3 pt-4">
        <Button 
          type="submit" 
          disabled={isLoading}
          className="flex-1"
        >
          {isLoading ? 'Saving...' : initialData ? 'Update Customer' : 'Create Customer'}
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