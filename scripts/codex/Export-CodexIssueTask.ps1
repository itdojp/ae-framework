<#
.SYNOPSIS
Exports a GitHub Issue into a local Codex CLI task file.

.DESCRIPTION
Uses `gh issue view` to write Issue title, URL, metadata, Context Pack preflight,
and body into `.codex-local/tasks/issue-N.md`. The output is local operator
input and must not be staged or committed.

.PARAMETER Repo
Repository in owner/name form.

.PARAMETER Issue
GitHub Issue number.

.PARAMETER Work
Repository or dedicated worktree root where `.codex-local/tasks/` should be created.

.PARAMETER OutFile
Optional output path. Relative paths are resolved under Work and must remain under Work.

.PARAMETER NoPreflight
Do not include the Context Pack preflight block.

.PARAMETER PrintCommands
Print dedicated worktree and non-interactive Codex CLI examples after writing.

.PARAMETER Help
Prints usage without invoking gh.
#>
[CmdletBinding()]
param(
  [string]$Repo = "itdojp/ae-framework",
  [int]$Issue,
  [string]$Work = (Get-Location).Path,
  [string]$OutFile,
  [string]$GeneratedAt = ([DateTime]::UtcNow.ToString("o")),
  [switch]$NoPreflight,
  [switch]$PrintCommands,
  [switch]$Help
)

function Show-Usage {
  @"
Usage:
  pwsh -NoProfile -File scripts/codex/Export-CodexIssueTask.ps1 -Repo itdojp/ae-framework -Issue 3490 -Work C:/path/to/ae-framework

Outputs:
  <Work>/.codex-local/tasks/issue-<Issue>.md

Notes:
  - Requires GitHub CLI (`gh`) authentication.
  - The task file is local operator input. Do not stage or commit `.codex-local/tasks/`.
  - Use a dedicated worktree for parallel Issue work.
"@
}

function Assert-UnderRoot {
  param(
    [Parameter(Mandatory = $true)][string]$Root,
    [Parameter(Mandatory = $true)][string]$Path
  )
  $rootFull = [System.IO.Path]::GetFullPath($Root)
  $pathFull = [System.IO.Path]::GetFullPath($Path)
  $comparison = [System.StringComparison]::OrdinalIgnoreCase
  if ($IsLinux -or $IsMacOS) {
    $comparison = [System.StringComparison]::Ordinal
  }
  $rootWithSeparator = $rootFull.TrimEnd([System.IO.Path]::DirectorySeparatorChar, [System.IO.Path]::AltDirectorySeparatorChar) + [System.IO.Path]::DirectorySeparatorChar
  if (($pathFull -ne $rootFull) -and (-not $pathFull.StartsWith($rootWithSeparator, $comparison))) {
    throw "OutFile must stay under Work: $pathFull"
  }
}

function Get-NearestExistingAncestor {
  param([Parameter(Mandatory = $true)][string]$Path)
  $current = [System.IO.Path]::GetFullPath($Path)
  while (-not (Test-Path -LiteralPath $current)) {
    $parent = [System.IO.Directory]::GetParent($current)
    if ($null -eq $parent) {
      throw "No existing ancestor found for output path: $Path"
    }
    $current = $parent.FullName
  }
  return $current
}

function Get-ResolvedProviderPath {
  param([Parameter(Mandatory = $true)][string]$Path)
  return [System.IO.Path]::GetFullPath((Resolve-Path -LiteralPath $Path -ErrorAction Stop).ProviderPath)
}

function Assert-ResolvedUnderRoot {
  param(
    [Parameter(Mandatory = $true)][string]$Root,
    [Parameter(Mandatory = $true)][string]$Path,
    [Parameter(Mandatory = $true)][string]$Context
  )
  $rootResolved = Get-ResolvedProviderPath -Path $Root
  $pathResolved = Get-ResolvedProviderPath -Path $Path
  try {
    Assert-UnderRoot -Root $rootResolved -Path $pathResolved
  } catch {
    throw "$Context must stay under Work after resolving symlinks: $pathResolved"
  }
}

function Assert-OutputFileIsNotLink {
  param([Parameter(Mandatory = $true)][string]$Path)
  $item = Get-Item -LiteralPath $Path -Force -ErrorAction SilentlyContinue
  if ($item -and (($item.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -ne 0)) {
    throw "Output file must not be a symbolic link: $Path"
  }
}

function ConvertTo-SingleQuotedArgument {
  param([Parameter(Mandatory = $true)][string]$Value)
  return "'" + ($Value -replace "'", "''") + "'"
}

function Get-ContextPackPreflight {
  @"
## Context Pack preflight

- Read ``AGENTS.md``.
- Read ``docs/spec/context-pack.md`` and ``spec/context-pack/boundary-map.json``.
- Identify the Context Pack ``objects``, ``morphisms``, ``diagrams``, ``acceptance_tests``, and existing tests relevant to the Issue target files.
- If the requested change conflicts with Context Pack constraints or the boundary map, stop before implementation and record ``Context Pack conflict: found`` with the conflicting IDs/paths in the PR or Issue comment.
- If no conflict is found, record ``Context Pack conflict: none`` in the PR body.
- Do not promote routine changes to MBT, property, or formal lanes unless the Issue, risk label, assurance profile, or critical-core boundary requires it.
"@
}

if ($Help) {
  Show-Usage
  exit 0
}

if ($Issue -le 0) {
  Show-Usage
  throw "Issue must be a positive integer."
}

if ($Repo -notmatch '^[^/\s]+/[^/\s]+$') {
  throw "Repo must be in owner/name form."
}

$workRoot = [System.IO.Path]::GetFullPath($Work)
if ([string]::IsNullOrWhiteSpace($OutFile)) {
  $outputPath = Join-Path $workRoot ".codex-local/tasks/issue-$Issue.md"
} elseif ([System.IO.Path]::IsPathRooted($OutFile)) {
  $outputPath = [System.IO.Path]::GetFullPath($OutFile)
} else {
  $outputPath = [System.IO.Path]::GetFullPath((Join-Path $workRoot $OutFile))
}
Assert-UnderRoot -Root $workRoot -Path $outputPath
$existingAncestor = Get-NearestExistingAncestor -Path ([System.IO.Path]::GetDirectoryName($outputPath))
Assert-ResolvedUnderRoot -Root $workRoot -Path $existingAncestor -Context "Output directory"
if (Test-Path -LiteralPath $outputPath) {
  Assert-OutputFileIsNotLink -Path $outputPath
  Assert-ResolvedUnderRoot -Root $workRoot -Path $outputPath -Context "Output file"
}

$gh = Get-Command gh -ErrorAction SilentlyContinue
if (-not $gh) {
  throw "GitHub CLI (`gh`) is required."
}

$issueJsonRaw = & gh issue view $Issue --repo $Repo --json title,body,url
if ($LASTEXITCODE -ne 0) {
  throw "gh issue view failed for $Repo#$Issue."
}
$issueJson = $issueJsonRaw | ConvertFrom-Json

$sections = [System.Collections.Generic.List[string]]::new()
$sections.Add("# $($issueJson.title)")
$sections.Add(("Issue: {0}`nRepository: {1}`nIssue number: {2}`nExported at: {3}`n`nLocal task file: do not stage or commit this file. Keep it under ``.codex-local/tasks/``." -f $issueJson.url, $Repo, $Issue, $GeneratedAt))
if (-not $NoPreflight) {
  $sections.Add((Get-ContextPackPreflight))
}
$sections.Add("## Issue body`n`n$($issueJson.body)")
$task = ($sections -join "`n`n") + "`n"

$outputDirectory = [System.IO.Path]::GetDirectoryName($outputPath)
New-Item -ItemType Directory -Force -LiteralPath $outputDirectory | Out-Null
Assert-ResolvedUnderRoot -Root $workRoot -Path $outputDirectory -Context "Output directory"
if (Test-Path -LiteralPath $outputPath) {
  Assert-OutputFileIsNotLink -Path $outputPath
  Assert-ResolvedUnderRoot -Root $workRoot -Path $outputPath -Context "Output file"
}
Set-Content -LiteralPath $outputPath -Value $task -NoNewline -Encoding utf8

Write-Output "[codex-issue-task] wrote $outputPath"
Write-Output "[codex-issue-task] source $($issueJson.url)"
Write-Output "[codex-issue-task] do not stage .codex-local/tasks/ files"

if ($PrintCommands) {
  $sibling = Join-Path ([System.IO.Directory]::GetParent($workRoot).FullName) "ae-framework-$Issue-work"
  $quotedSibling = ConvertTo-SingleQuotedArgument -Value $sibling
  $quotedBranch = ConvertTo-SingleQuotedArgument -Value "work/issue-$Issue"
  $quotedOutputPath = ConvertTo-SingleQuotedArgument -Value $outputPath
  Write-Output ""
  Write-Output "# Dedicated worktree example"
  Write-Output "git fetch origin main --prune"
  Write-Output "git worktree add $quotedSibling -b $quotedBranch origin/main"
  Write-Output ""
  Write-Output "# Preflight reminder"
  Write-Output "# Read the Context Pack preflight block in the task file before implementation."
  Write-Output "# If constraints conflict, stop and record `"Context Pack conflict: found`"."
  Write-Output ""
  Write-Output "# Non-interactive Codex CLI example"
  Write-Output "Get-Content -Raw -LiteralPath $quotedOutputPath | codex exec --cd $quotedSibling --sandbox workspace-write --ask-for-approval never -"
}
