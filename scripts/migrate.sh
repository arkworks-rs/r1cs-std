#!/usr/bin/env bash

# -----------------------------------------------------------------------------
# rename_r1cs.sh (Regex Version)
# 
# Recursively:
# 1. Renames .rs filenames: R1CS->GR1CS, r1cs->gr1cs (except those with r1cs_std).
# 2. In .rs file contents, replaces R1CS->GR1CS, r1cs->gr1cs (except lines with r1cs_std),
#    ensuring words already in GR1CS/gr1cs are not changed again.
# 3. Finally replaces enforce_constraint->enforce_r1cs_constraint (except lines with r1cs_std),
#    ensuring enforce_r1cs_constraint is not changed again.
# -----------------------------------------------------------------------------

# --- Detect which 'sed' in-place flag to use (GNU vs BSD/macOS) ---
if sed --version 2>/dev/null | grep -q "GNU"; then
    SED_INPLACE=(-i)
else
    SED_INPLACE=(-i '')
fi

echo "###############################################"
echo "#  Make sure you have a backup before running. #"
echo "###############################################"
echo
read -p "Are you sure you want to continue? (yes/no) " choice

if [[ "$choice" != "yes" ]]; then
    echo "Aborting script execution."
    exit 1
fi

# 1) Rename files that contain 'r1cs' or 'R1CS' in their name, skipping 'r1cs_std' and existing 'gr1cs'.
echo "Renaming files that contain 'r1cs' or 'R1CS' (but not 'r1cs_std' and already converted ones)..."
export LC_ALL=C # Ensure consistent behavior for case conversions

while IFS= read -r -d '' file; do
    if [[ "$file" =~ r1cs_std || "$file" =~ gr1cs ]]; then
        continue
    fi
    newfile="$(echo "$file" | sed -E 's/(^|[^g])r1cs/\1gr1cs/g; s/(^|[^G])R1CS/\1GR1CS/g')"
    if [[ "$newfile" != "$file" ]]; then
        echo " -> Renaming: $file -> $newfile"
        mv "$file" "$newfile"
    fi
done < <(find . -type f -name "*.rs" -print0)

# 2) Replace R1CS->GR1CS and r1cs->gr1cs in file contents,
#    skipping lines that have 'r1cs_std' and ensuring already transformed words are not changed again.
echo "Replacing (R1CS->GR1CS, r1cs->gr1cs) in .rs file contents..."
while IFS= read -r -d '' file; do
    sed "${SED_INPLACE[@]}" -E '/r1cs_std|enforce_r1cs_constraint/! s/(^|[^g])r1cs/\1gr1cs/g' "$file"
    sed "${SED_INPLACE[@]}" -E '/r1cs_std|enforce_r1cs_constraint/! s/(^|[^G])R1CS/\1GR1CS/g' "$file"
done < <(find . -type f -name "*.rs" ! -name "*r1cs_std*" -print0)

# 3) Replace 'enforce_constraint' -> 'enforce_r1cs_constraint',
#    skipping lines that have 'r1cs_std' and ensuring enforce_r1cs_constraint is not changed again.
echo "Replacing enforce_constraint->enforce_r1cs_constraint..."
while IFS= read -r -d '' file; do
    sed "${SED_INPLACE[@]}" '/r1cs_std|enforce_r1cs_constraint/! s/enforce_constraint/enforce_r1cs_constraint/g' "$file"
done < <(find . -type f -name "*.rs" ! -name "*r1cs_std*" -print0)

echo "Done!"
