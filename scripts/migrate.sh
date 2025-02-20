#!/usr/bin/env bash

# -----------------------------------------------------------------------------
# rename_r1cs.sh
#
# Recursively:
# 1. Renames .rs filenames: R1CS->GR1CS, r1cs->gr1cs (except those with r1cs_std).
# 2. In .rs file contents, replaces R1CS->GR1CS, r1cs->gr1cs (except lines with r1cs_std).
# 3. Finally replaces enforce_constraint->enforce_r1cs_constraint (except lines with r1cs_std).
# -----------------------------------------------------------------------------

# --- Detect which 'sed' in-place flag to use (GNU vs BSD/macOS) ---
# On macOS, 'sed -i' requires a backup extension parameter (can be empty '').
# On GNU sed, 'sed -i' is fine without extra args.
if sed --version 2>/dev/null | grep -q "GNU"; then
    # GNU sed
    SED_INPLACE=(-i)
else
    # BSD/macOS sed
    SED_INPLACE=(-i '')
fi

echo "###############################################"
echo "#  ⚠️  Cautious: RUN THIS SCRIPT ONLY ONCE! DO NOT RUN IT TWICE!  #"
echo "#  Make sure you have a backup before running. #"
echo "###############################################"
echo
read -p "Are you sure you want to continue? (yes/no) " choice

if [[ "$choice" != "yes" ]]; then
    echo "Aborting script execution."
    exit 1
fi

# 1) Rename files that contain 'r1cs' or 'R1CS' in their name, skipping any with 'r1cs_std'.
echo "Renaming files that contain 'r1cs' or 'R1CS' (but not 'r1cs_std')..."
export LC_ALL=C # Ensure consistent behavior for case conversions

# Use 'find' + 'while IFS= read -r -d ""' to handle spaces & special chars in filenames.
while IFS= read -r -d '' file; do
    # If filename includes r1cs_std, skip
    if [[ "$file" =~ r1cs_std ]]; then
        continue
    fi

    # Compute new filename by substituting:
    newfile="$(echo "$file" | sed 's/R1CS/GR1CS/g; s/r1cs/gr1cs/g')"

    if [[ "$newfile" != "$file" ]]; then
        echo " -> Renaming: $file -> $newfile"
        mv "$file" "$newfile"
    fi
done < <(find . -type f -name "*.rs" -print0)

# 2) Replace R1CS->GR1CS and r1cs->gr1cs in file contents,
#    skipping lines that have 'r1cs_std'.
echo "Replacing (R1CS->GR1CS, r1cs->gr1cs) in .rs file contents..."
while IFS= read -r -d '' file; do
    # Replace R1CS -> GR1CS on lines NOT containing 'r1cs_std'
    sed "${SED_INPLACE[@]}" '/r1cs_std/! s/R1CS/GR1CS/g' "$file"
    # Replace r1cs -> gr1cs on lines NOT containing 'r1cs_std'
    sed "${SED_INPLACE[@]}" '/r1cs_std/! s/r1cs/gr1cs/g' "$file"
done < <(find . -type f -name "*.rs" ! -name "*r1cs_std*" -print0)

# 3) Finally, replace 'enforce_constraint' -> 'enforce_r1cs_constraint',
#    skipping lines that have 'r1cs_std'.
echo "Replacing enforce_constraint->enforce_r1cs_constraint..."
while IFS= read -r -d '' file; do
    sed "${SED_INPLACE[@]}" '/r1cs_std/! s/enforce_constraint/enforce_r1cs_constraint/g' "$file"
done < <(find . -type f -name "*.rs" ! -name "*r1cs_std*" -print0)

echo "Done!"
