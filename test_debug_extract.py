#!/usr/bin/env python3
import yaml
from aletheia import CANDecoder

# Load DBC
decoder = CANDecoder.from_dbc("test_dbc.yaml")

# Build command YAML (same as in extract_signal method)
frame_bytes = [0x10, 0x27, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
frame_hex = " ".join(f"0x{b:02X}" for b in frame_bytes)

dbc_yaml_str = yaml.dump(decoder.dbc_data, default_flow_style=False)
command_yaml = f'''command: "ExtractSignal"
message: "EngineData"
signal: "EngineSpeed"
frame: {frame_hex}
yaml: |
'''
for line in dbc_yaml_str.splitlines():
    if line.strip():
        command_yaml += f'  {line}\n'
    else:
        command_yaml += '\n'

print("=== GENERATED YAML ===")
print(command_yaml)
print("=== END ===")
