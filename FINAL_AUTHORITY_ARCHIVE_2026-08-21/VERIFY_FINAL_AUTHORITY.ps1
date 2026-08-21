[CmdletBinding()]
param(
  [string]$RepoDir = (Get-Location).Path,
  [switch]$FullLean
)
$ErrorActionPreference = "Stop"
$AuthorityCommit = "61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3"
$Tag = "formalization-final-2026-08-21"
$EvidenceSha256 = "86b2525c7533562b929a573eca0ff006c6b1df1ac054329c906eae009e05954a"
$ManifestSha256 = "672474eb93bc14c66cd1ff45203c451987fe525f7b5d13ecd83140be46434b26"
$Toolchain = "leanprover/lean4:v4.33.0-rc1"
$PackageDir = Split-Path -Parent $MyInvocation.MyCommand.Path

function Fail([string]$Message) { throw "VERIFY_FINAL_AUTHORITY: FAIL: $Message" }
if (-not (Get-Command git -ErrorAction SilentlyContinue)) { Fail "git is required" }

$SumsPath = Join-Path $PackageDir "SHA256SUMS.txt"
if (-not (Test-Path -LiteralPath $SumsPath -PathType Leaf)) { Fail "missing SHA256SUMS.txt" }
foreach ($Line in Get-Content -LiteralPath $SumsPath) {
  if ([string]::IsNullOrWhiteSpace($Line)) { continue }
  $Parts = $Line -split '\s+', 2
  $Expected = $Parts[0].ToLowerInvariant()
  $Name = $Parts[1].TrimStart(' ', '*')
  $Path = Join-Path $PackageDir $Name
  if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) { Fail "missing package file: $Name" }
  $Actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
  if ($Actual -ne $Expected) { Fail "SHA256 mismatch for $Name: $Actual != $Expected" }
}
Write-Host "package SHA256SUMS: PASS"

$Evidence = Join-Path $PackageDir "final-authority-last-mile-32438949135-attempt1.zip"
$ActualEvidence = (Get-FileHash -Algorithm SHA256 -LiteralPath $Evidence).Hash.ToLowerInvariant()
if ($ActualEvidence -ne $EvidenceSha256) { Fail "original evidence ZIP SHA256 mismatch" }
$Temp = Join-Path ([System.IO.Path]::GetTempPath()) ("final-authority-" + [guid]::NewGuid().ToString())
New-Item -ItemType Directory -Path $Temp | Out-Null
try {
  Expand-Archive -LiteralPath $Evidence -DestinationPath $Temp
  $A = Join-Path $Temp ".final_authority"
  function Load-Json([string]$Name) { Get-Content -Raw -LiteralPath (Join-Path $A $Name) | ConvertFrom-Json -AsHashtable }
  $F13 = Load-Json "FINAL_13_BUILD_RESULTS.json"
  $BA = Load-Json "BUILDALL_RESULT.json"
  $C1 = Load-Json "CLEAN_BUILD_1_RESULT.json"
  $C2 = Load-Json "CLEAN_BUILD_2_RESULT.json"
  $CK = Load-Json "FINAL_15_CHECKLIST_RESULT.json"
  $FO = Load-Json "FORBIDDEN_AUDIT.json"
  $AX = Load-Json "AXIOM_AUDIT.json"
  $ID = Load-Json "FINAL_SOURCE_IDENTITY.json"
  if (-not $F13.pass -or $F13.counts.PASS -ne 13 -or $F13.counts.FAIL -ne 0 -or $F13.counts.SKIPPED -ne 0 -or $F13.counts.NOT_RUN -ne 0) { Fail "Final13 counts mismatch" }
  if ($F13.bridge_counts.PASS -ne 2 -or $F13.bridge_counts.FAIL -ne 0 -or $F13.bridge_counts.SKIPPED -ne 0 -or $F13.bridge_counts.NOT_RUN -ne 0) { Fail "bridge counts mismatch" }
  $AR = $BA.aggregate_result
  if (-not $BA.pass -or $AR.exit -ne 0 -or $AR.error_headers -ne 0 -or $AR.panic_lines -ne 0 -or $AR.sorry_warning_lines -ne 0) { Fail "BuildAll mismatch" }
  if (-not $C1.pass -or -not $C2.pass -or $C1.source_commit -ne $AuthorityCommit -or $C2.source_commit -ne $AuthorityCommit) { Fail "clean build mismatch" }
  if (-not $CK.pass -or $CK.counts.PASS -ne 15 -or $CK.counts.FAIL -ne 0 -or $CK.counts.SKIPPED -ne 0 -or $CK.counts.NOT_RUN -ne 0) { Fail "checklist mismatch" }
  if (-not $FO.pass -or $FO.forbidden_count -ne 0) { Fail "forbidden audit mismatch" }
  if (-not $AX.pass) { Fail "axiom audit mismatch" }
  if (-not $ID.pass -or $ID.tested_source_commit -ne $AuthorityCommit) { Fail "source identity mismatch" }
  Write-Host "evidence JSON consistency: PASS"
} finally {
  Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue
}

if (-not (Test-Path -LiteralPath (Join-Path $RepoDir ".git"))) { Fail "RepoDir is not a Git working tree: $RepoDir" }
$Head = (& git -C $RepoDir rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $Head -ne $AuthorityCommit) { Fail "HEAD $Head does not equal authority commit" }
$Target = (& git -C $RepoDir rev-parse "$Tag^{}").Trim()
if ($LASTEXITCODE -ne 0 -or $Target -ne $AuthorityCommit) { Fail "tag target $Target does not equal authority commit" }
$TagType = (& git -C $RepoDir cat-file -t "refs/tags/$Tag").Trim()
if ($LASTEXITCODE -ne 0 -or $TagType -ne "tag") { Fail "canonical tag is not annotated (type=$TagType)" }
$Dirty = (& git -C $RepoDir status --porcelain --untracked-files=no)
if ($LASTEXITCODE -ne 0 -or $Dirty) { Fail "tracked working tree is dirty" }

$Record = Get-Content -Raw -LiteralPath (Join-Path $PackageDir "FINAL_AUTHORITY_RECORD.json") | ConvertFrom-Json
$Rows = @($Record.primary_roots) + @($Record.bridges) + @($Record.buildall_fingerprint)
foreach ($Row in $Rows) {
  $Path = Join-Path $RepoDir $Row.path
  if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) { Fail "missing source: $($Row.path)" }
  $Actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
  if ($Actual -ne $Row.sha256) { Fail "source SHA256 mismatch: $($Row.path)" }
  $Blob = (& git -C $RepoDir hash-object --no-filters $Row.path).Trim()
  if ($LASTEXITCODE -ne 0 -or $Blob -ne $Row.git_blob) { Fail "Git blob mismatch: $($Row.path)" }
}
$Manifest = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $RepoDir "lake-manifest.json")).Hash.ToLowerInvariant()
if ($Manifest -ne $ManifestSha256) { Fail "lake-manifest SHA256 mismatch" }
if ((Get-Content -Raw -LiteralPath (Join-Path $RepoDir "lean-toolchain")).Trim() -ne $Toolchain) { Fail "lean-toolchain mismatch" }
Write-Host "source fingerprints and manifest: PASS"

if ($FullLean -or $env:FULL_LEAN -eq "1") {
  Push-Location $RepoDir
  try {
    & python3 scripts/final_authority_gate_v5.py
    if ($LASTEXITCODE -ne 0) { Fail "optional full Lean reproduction failed" }
  } finally { Pop-Location }
}
Write-Host "VERIFY_FINAL_AUTHORITY: PASS"
