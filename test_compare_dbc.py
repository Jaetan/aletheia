#!/usr/bin/env python3
import yaml

# Original DBC file (what works)
with open("test_dbc.yaml", 'r') as f:
    original = f.read()
    
print("=== ORIGINAL DBC (WORKS) ===")
print(original)

# What Python yaml.dump() generates
with open("test_dbc.yaml", 'r') as f:
    data = yaml.safe_load(f)
    
regenerated = yaml.dump(data, default_flow_style=False)
print("\n=== PYTHON yaml.dump() (FAILS) ===")
print(regenerated)

print("\n=== DIFFERENCES ===")
print("1. Original uses quoted strings for some values")
print("2. Python may use different indentation")
print("3. Python may reorder fields")
