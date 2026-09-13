import os, re, sys

# Collect all sovereign .agda files (excluding All.agda)
sovereign_files = []
for root, dirs, files in os.walk('src/Sovereign'):
    for f in files:
        if f.endswith('.agda') and f != 'All.agda':
            sovereign_files.append(os.path.join(root, f))

# For each file, extract its module name and its imports
file_module = {}
module_imports = {}

for fp in sovereign_files:
    with open(fp, 'r', errors='replace') as fh:
        content = fh.read()
    
    # Extract module declaration
    m = re.search(r'module\s+(Sovereign\.\S+)', content)
    if m:
        mod = m.group(1)
        file_module[fp] = mod
    
    # Extract imports
    imports = re.findall(r'(?:open\s+)?import\s+(Sovereign\.\S+)', content)
    module_imports[fp] = set(imports)

# Registered modules in All.agda
registered = set()
with open('src/Sovereign/All.agda') as f:
    for line in f:
        m = re.search(r'import\s+(Sovereign\.\S+)', line)
        if m:
            registered.add(m.group(1))

print(f'Registered in All.agda: {len(registered)}')
print(f'Total Sovereign files: {len(sovereign_files)}')

# Find unregistered files
unregistered = {}
for fp, mod in file_module.items():
    if mod not in registered:
        unregistered[fp] = mod

print(f'Unregistered modules: {len(unregistered)}')

# Now find which unregistered modules are imported by registered ones
# These MUST compile since the registered ones compile
imported_by_registered = set()
for fp, imps in module_imports.items():
    mod = file_module.get(fp)
    if mod and mod in registered:
        imported_by_registered.update(imps)

# Of those imported by registered, which are unregistered?
transitive_safe = set()
for mod in imported_by_registered:
    if mod in unregistered.values():
        transitive_safe.add(mod)

print(f'\nUnregistered but imported by registered modules ({len(transitive_safe)}):')
for m in sorted(transitive_safe):
    print(f'  {m}')

# Unregistered AND not imported by any registered module
truly_orphan = set()
for fp, mod in unregistered.items():
    if mod not in imported_by_registered:
        truly_orphan.add(mod)

print(f'\nUnregistered AND not imported by registered ({len(truly_orphan)}):')
for m in sorted(truly_orphan):
    print(f'  {m}')
