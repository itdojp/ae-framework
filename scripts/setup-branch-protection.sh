#!/usr/bin/env bash
set -euo pipefail

# Branch Protection Setup for ae-framework
#
# This script configures branch protection rules for the main branch with:
# - Required status check: "verify / verify" 
# - Strict status checks (up-to-date before merge)
# - Required PR reviews (1 approver)
# - Admin enforcement
#
# Requirements:
# - GitHub CLI authenticated with admin privileges on this repository
# - Repository must have at least one successful "verify / verify" status check
#
# Usage:
#   ./scripts/setup-branch-protection.sh
#
# Note: This requires repository admin privileges to execute

echo "🔒 Branch Protection Setup for ae-framework"
echo "This requires admin privileges on the repository."
echo ""

# Get repository information from GitHub CLI
OWNER=$(gh repo view --json owner,name -q '.owner.login')
REPO=$(gh repo view --json owner,name -q '.name')

echo "Repository: $OWNER/$REPO"
echo "Configuring branch protection for main branch..."
echo ""

# Check if branch protection already exists
if gh api "repos/$OWNER/$REPO/branches/main/protection" >/dev/null 2>&1; then
  echo "✅ Branch protection already configured for main branch"
  echo "Current settings:"
  gh api "repos/$OWNER/$REPO/branches/main/protection" --jq '.required_status_checks.contexts[]' | sed 's/^/  - /'
  echo ""
  echo "To update settings, the script will proceed with reconfiguration..."
  echo ""
else
  echo "⚠️  No branch protection currently configured"
  echo ""
fi

# Configure branch protection
echo "Setting up branch protection with required check: 'verify / verify'..."

gh api "repos/$OWNER/$REPO/branches/main/protection" \
  --method PUT \
  -f required_status_checks.strict=true \
  -f required_status_checks.contexts[]="verify / verify" \
  -f enforce_admins=true \
  -f required_pull_request_reviews.required_approving_review_count=1 \
  -f restrictions="" \
  >/dev/null

echo "✅ Done! Branch protection configured successfully."
echo ""
echo "📋 Summary:"
echo "  - Required status check: verify / verify"
echo "  - Strict status checks: enabled"
echo "  - Required PR reviews: 1"
echo "  - Admin enforcement: enabled"
echo ""
echo "🚨 Important: Ensure that 'verify / verify' status check exists by:"
echo "   1. Creating a PR or pushing to a branch"
echo "   2. Waiting for the PR Verify workflow to complete"
echo "   3. The status check will appear as 'verify / verify' in the PR"