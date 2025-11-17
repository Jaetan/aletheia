#!/usr/bin/env python3
"""Test manual YAML construction with multiline literal"""

import subprocess

# Read DBC content
with open("test_dbc.yaml", 'r') as f:
    dbc_content = f.read()

# Build YAML manually with literal block
command_yaml = 'command: "ParseDBC"\nyaml: |\n'
for line in dbc_content.splitlines():
    # Only add indentation to non-empty lines
    if line.strip():
        command_yaml += f'  {line}\n'
    else:
        command_yaml += '\n'

print("=== MANUAL YAML ===")
print(command_yaml)
print("=== END ===")

# Test with binary
result = subprocess.run(
    ["./build/aletheia"],
    input=command_yaml.encode('utf-8'),
    capture_output=True,
    timeout=10
)

print("\n=== BINARY RESPONSE ===")
print(result.stdout.decode('utf-8'))
if result.stderr:
    print("\n=== STDERR ===")
    print(result.stderr.decode('utf-8'))
