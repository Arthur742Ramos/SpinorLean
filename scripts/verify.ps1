$ErrorActionPreference = "Stop"

lake build Spinor Challenge Solution

$leanFiles = @(
    Get-ChildItem -Path "Spinor" -Recurse -Filter "*.lean"
    Get-Item -Path "Spinor.lean"
)

$matches = Select-String -Path ($leanFiles | ForEach-Object { $_.FullName }) `
    -Pattern '\b(sorry|admit|axiom|unsafe)\b'

if ($matches) {
    $matches
    Write-Error "Forbidden proof-hole token found in Lean source."
    exit 1
}
