[CmdletBinding()]
param(
  [string]$RepoDir = (Get-Location).Path,
  [string]$PackageDir = (Split-Path -Parent $MyInvocation.MyCommand.Path)
)
$ErrorActionPreference = 'Stop'
$Repository = 'leegahuyn/mathlib4'
$AuthorityCommit = '61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3'
$Tag = 'formalization-final-2026-08-21'
$Title = 'Formalization FINAL AUTHORITY — 2026-08-21'
$PrNumber = 56
$RunId = '32438949135'
$EvidenceSha256 = '86b2525c7533562b929a573eca0ff006c6b1df1ac054329c906eae009e05954a'
function Fail([string]$Message) { throw "FINAL AUTHORITY PUBLICATION: FAIL: $Message" }
foreach ($Command in @('git','gh')) { if (-not (Get-Command $Command -ErrorAction SilentlyContinue)) { Fail "$Command is required" } }
if (-not $env:GH_TOKEN) { Fail 'set GH_TOKEN to a token with Contents:write and Workflows:write (or classic repo+workflow)' }
& gh auth status *> $null; if ($LASTEXITCODE -ne 0) { Fail 'gh authentication failed' }
if (-not (Test-Path -LiteralPath (Join-Path $RepoDir '.git'))) { Fail "not a Git working tree: $RepoDir" }

foreach ($Line in Get-Content -LiteralPath (Join-Path $PackageDir 'SHA256SUMS.txt')) {
  if ([string]::IsNullOrWhiteSpace($Line)) { continue }
  $Parts = $Line -split '\s+', 2
  $Name = $Parts[1].TrimStart(' ', '*')
  $Path = Join-Path $PackageDir $Name
  if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) { Fail "missing package file: $Name" }
  $Actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
  if ($Actual -ne $Parts[0].ToLowerInvariant()) { Fail "SHA256 mismatch: $Name" }
}

& git -C $RepoDir fetch origin $AuthorityCommit --no-tags
if ($LASTEXITCODE -ne 0) { Fail 'authority commit fetch failed' }
if ((& git -C $RepoDir rev-parse "$AuthorityCommit^{commit}").Trim() -ne $AuthorityCommit) { Fail 'authority commit missing' }
$RemoteTag = (& git -C $RepoDir ls-remote --tags origin "refs/tags/$Tag" "refs/tags/$Tag^{}").Trim()
if ($RemoteTag) {
  & git -C $RepoDir fetch --force origin "refs/tags/${Tag}:refs/tags/${Tag}"
  if ((& git -C $RepoDir cat-file -t "refs/tags/$Tag").Trim() -ne 'tag') { Fail 'existing canonical ref is not annotated' }
  if ((& git -C $RepoDir rev-parse "refs/tags/$Tag^{}").Trim() -ne $AuthorityCommit) { Fail 'TAG_ALREADY_EXISTS_WRONG_TARGET' }
} else {
  $Message = @"
Formalization FINAL AUTHORITY
Exact tested commit: $AuthorityCommit
Actual Lean authority run: $RunId
Job: 96645636205
Final13 13/13; bridges 2/2; BuildAll PASS; clean×2 PASS;
checklist 15/15; forbidden 0; panic 0; axiom/source identity PASS.
Evidence ZIP SHA256:
$EvidenceSha256
"@
  $MessageFile = [IO.Path]::GetTempFileName()
  try {
    Set-Content -LiteralPath $MessageFile -Value $Message -NoNewline
    & git -C $RepoDir tag -a $Tag $AuthorityCommit -F $MessageFile
    if ($LASTEXITCODE -ne 0) { Fail 'annotated tag creation failed' }
    & git -C $RepoDir push origin "refs/tags/$Tag"
    if ($LASTEXITCODE -ne 0) { Fail 'annotated tag push failed' }
  } finally { Remove-Item -LiteralPath $MessageFile -Force -ErrorAction SilentlyContinue }
}

& git -C $RepoDir fetch --force origin "refs/tags/${Tag}:refs/tags/${Tag}"
if ((& git -C $RepoDir cat-file -t "refs/tags/$Tag").Trim() -ne 'tag') { Fail 'canonical tag is not annotated' }
if ((& git -C $RepoDir rev-parse "refs/tags/$Tag^{}").Trim() -ne $AuthorityCommit) { Fail 'canonical tag target mismatch' }

& gh release view $Tag --repo $Repository --json tagName,name,url *> $null
if ($LASTEXITCODE -ne 0) {
  & gh release create $Tag --repo $Repository --verify-tag --title $Title --notes-file (Join-Path $PackageDir 'RELEASE_NOTES.md')
  if ($LASTEXITCODE -ne 0) { Fail 'release creation failed' }
}
$Assets = @(
  'final-authority-last-mile-32438949135-attempt1.zip','FINAL_AUTHORITY_RECORD.json','FINAL_AUTHORITY_RECORD.md',
  'SHA256SUMS.txt','VERIFY_FINAL_AUTHORITY.sh','VERIFY_FINAL_AUTHORITY.ps1','formalization-final-source-61a48f07.tar.gz',
  'RELEASE_NOTES.md','FINAL_TRUE_PASS_REPORT.md','FINAL_STATUS_CARD.md','FINAL_SOURCE_IDENTITY.json',
  'FINAL_15_CHECKLIST_RESULT.json','CLEAN_BUILD_1_RESULT.json','CLEAN_BUILD_2_RESULT.json','BUILDALL_RESULT.json',
  'FINAL_13_BUILD_RESULTS.json','FORBIDDEN_AUDIT.json','AXIOM_AUDIT.json','QYM_CANONICAL_REPLAY_RESULT.json','MOCK3_CANONICAL_RESULT.json'
)
$Existing = @(& gh release view $Tag --repo $Repository --json assets --jq '.assets[].name')
foreach ($Name in $Assets) {
  $Path = Join-Path $PackageDir $Name
  if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) { Fail "missing release asset: $Name" }
  if ($Existing -contains $Name) {
    $Temp = Join-Path ([IO.Path]::GetTempPath()) ([guid]::NewGuid().ToString())
    New-Item -ItemType Directory -Path $Temp | Out-Null
    try {
      & gh release download $Tag --repo $Repository --pattern $Name --dir $Temp
      if ($LASTEXITCODE -ne 0) { Fail "release asset download failed: $Name" }
      if ((Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $Temp $Name)).Hash -ne (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash) { Fail "existing release asset hash mismatch: $Name" }
    } finally { Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue }
  } else {
    & gh release upload $Tag $Path --repo $Repository
    if ($LASTEXITCODE -ne 0) { Fail "release asset upload failed: $Name" }
  }
}
$Release = (& gh release view $Tag --repo $Repository --json tagName,name,url | ConvertFrom-Json)
$Marker = '<!-- formalization-final-2026-08-21-archive -->'
$Body = @"
$Marker
FINAL AUTHORITY archived.

Canonical tag:
$Tag

Exact authority commit:
$AuthorityCommit

Authority run:
$RunId

Evidence SHA256:
$EvidenceSha256

Release:
$($Release.url)

No merge commit supersedes this authority.
Future development requires a successor version.
"@
$Comments = @(& gh api --paginate "repos/$Repository/issues/$PrNumber/comments?per_page=100" | ConvertFrom-Json)
$ExistingComment = $Comments | Where-Object { $_.body.Contains($Marker) } | Select-Object -First 1
if (-not $ExistingComment) {
  & gh api --method POST "repos/$Repository/issues/$PrNumber/comments" -f body="$Body" *> $null
  if ($LASTEXITCODE -ne 0) { Fail 'PR archive comment failed' }
} elseif ($ExistingComment.body -ne $Body) { Fail 'existing archive PR comment differs' }
Write-Host 'FINAL AUTHORITY PUBLICATION: PASS'
Write-Host "Tag target: $((& git -C $RepoDir rev-parse "refs/tags/$Tag^{}").Trim())"
Write-Host "Release: $($Release.url)"
