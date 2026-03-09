'use client';

import { useState } from 'react';

export default function SemanticFormPage() {
  const [teamName, setTeamName] = useState('');
  const [ownerEmail, setOwnerEmail] = useState('');
  const [confirmed, setConfirmed] = useState(false);
  const [errors, setErrors] = useState<string[]>([]);
  const [submittedMessage, setSubmittedMessage] = useState('');

  const handleSubmit = (event: React.FormEvent<HTMLFormElement>) => {
    event.preventDefault();
    const nextErrors: string[] = [];

    if (!teamName.trim()) {
      nextErrors.push('Team name is required.');
    }
    if (!ownerEmail.trim()) {
      nextErrors.push('Owner email is required.');
    }
    if (!confirmed) {
      nextErrors.push('Accessibility confirmation is required.');
    }

    setErrors(nextErrors);
    if (nextErrors.length > 0) {
      setSubmittedMessage('');
      return;
    }

    setSubmittedMessage(`Submitted semantic form for ${teamName.trim()}`);
  };

  return (
    <main className="container mx-auto max-w-2xl px-4 py-8">
      <h1 className="mb-2 text-3xl font-bold text-gray-900">Semantic Form Demo</h1>
      <p className="mb-6 text-gray-600">
        Minimal accessible form used by the semantic UI E2E lane.
      </p>

      {errors.length > 0 && (
        <div role="alert" className="mb-6 rounded-md border border-red-200 bg-red-50 p-4 text-red-800">
          <h2 className="mb-2 text-base font-semibold">Validation errors</h2>
          <ul className="list-disc pl-5">
            {errors.map((error) => (
              <li key={error}>{error}</li>
            ))}
          </ul>
        </div>
      )}

      {submittedMessage && (
        <p role="status" className="mb-6 rounded-md border border-green-200 bg-green-50 p-4 text-green-800">
          {submittedMessage}
        </p>
      )}

      <form className="space-y-6 rounded-lg border bg-white p-6" onSubmit={handleSubmit}>
        <div>
          <label className="mb-1 block text-sm font-medium text-gray-700" htmlFor="team-name">
            Team name
          </label>
          <input
            id="team-name"
            name="teamName"
            value={teamName}
            onChange={(event) => setTeamName(event.target.value)}
            placeholder="Platform QA"
            className="w-full rounded-md border border-gray-300 px-3 py-2 text-gray-900 shadow-sm focus:border-blue-500 focus:outline-none focus:ring-2 focus:ring-blue-200"
          />
        </div>

        <div>
          <label className="mb-1 block text-sm font-medium text-gray-700" htmlFor="owner-email">
            Owner email
          </label>
          <input
            id="owner-email"
            name="ownerEmail"
            type="email"
            value={ownerEmail}
            onChange={(event) => setOwnerEmail(event.target.value)}
            placeholder="qa@example.com"
            className="w-full rounded-md border border-gray-300 px-3 py-2 text-gray-900 shadow-sm focus:border-blue-500 focus:outline-none focus:ring-2 focus:ring-blue-200"
          />
        </div>

        <div className="flex items-center gap-3">
          <input
            id="confirm-accessible"
            type="checkbox"
            checked={confirmed}
            onChange={(event) => setConfirmed(event.target.checked)}
            className="h-4 w-4 rounded border-gray-300 text-blue-600 focus:ring-blue-500"
          />
          <label className="text-sm text-gray-700" htmlFor="confirm-accessible">
            I confirm the workflow is keyboard-accessible
          </label>
        </div>

        <button
          type="submit"
          className="inline-flex items-center rounded-md bg-blue-600 px-4 py-2 font-medium text-white hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-blue-300"
        >
          Submit Semantic Form
        </button>
      </form>
    </main>
  );
}
