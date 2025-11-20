"""CAN frame decoder"""

from pathlib import Path
from typing import Dict, Any, List, Union
import yaml

from aletheia._binary import get_binary_path
import subprocess


def _call_binary(command_yaml: str, timeout: int = 60) -> Dict[str, Any]:
    """Call the Aletheia binary with a command and return parsed response

    Args:
        command_yaml: YAML-formatted command string
        timeout: Timeout in seconds

    Returns:
        Parsed YAML response as dictionary

    Raises:
        RuntimeError: If binary call fails
    """
    binary = get_binary_path()

    try:
        result = subprocess.run(
            [str(binary)],
            input=command_yaml.encode('utf-8'),
            capture_output=True,
            check=True,
            timeout=timeout
        )

        response_yaml = result.stdout.decode('utf-8')
        return yaml.safe_load(response_yaml)
    except subprocess.CalledProcessError as e:
        stderr = e.stderr.decode('utf-8') if e.stderr else 'No error output'
        raise RuntimeError(f"Binary failed: {stderr}")
    except subprocess.TimeoutExpired:
        raise RuntimeError("Binary timed out")


class CANDecoder:
    """Decoder for CAN frames using DBC specification"""

    def __init__(self, dbc_data: Dict[str, Any], dbc_yaml: str = None):
        """Initialize decoder with DBC data

        Args:
            dbc_data: Parsed DBC YAML data
            dbc_yaml: Original DBC YAML string (to preserve hex formatting)
        """
        self.dbc_data = dbc_data
        self.dbc_yaml = dbc_yaml or yaml.dump(dbc_data, default_flow_style=False)
        self._messages = {msg['id']: msg for msg in dbc_data.get('messages', [])}

    @classmethod
    def from_dbc(cls, dbc_file: Union[str, Path]) -> 'CANDecoder':
        """Load and parse DBC from YAML file using verified parser

        Args:
            dbc_file: Path to DBC YAML file

        Returns:
            Configured CANDecoder instance

        Raises:
            FileNotFoundError: If DBC file doesn't exist
            RuntimeError: If parsing fails
        """
        dbc_path = Path(dbc_file)
        if not dbc_path.exists():
            raise FileNotFoundError(f"DBC file not found: {dbc_file}")

        # Read the DBC YAML file
        with open(dbc_path, 'r') as f:
            dbc_yaml_content = f.read()

        # Call binary to parse DBC (uses verified Agda parser)
        # Build the command YAML manually to preserve multiline literal format
        command_yaml = f'command: "ParseDBC"\nyaml: |\n'
        # Indent each line of DBC content by 2 spaces (skip indentation for empty lines)
        for line in dbc_yaml_content.splitlines():
            if line.strip():
                command_yaml += f'  {line}\n'
            else:
                command_yaml += '\n'

        # Call binary with formatted YAML
        response = _call_binary(command_yaml)

        # Check response status
        if not response.get('success'):
            error_msg = response.get('message', 'Unknown error')
            raise RuntimeError(f"Failed to parse DBC: {error_msg}")

        # Return decoder with parsed DBC data
        # Note: For Phase 1, we trust the binary's parsing
        # Phase 3 will add round-trip verification
        # IMPORTANT: Preserve original YAML to maintain hex formatting
        dbc_data = yaml.safe_load(dbc_yaml_content)
        return cls(dbc_data, dbc_yaml_content)

    def extract_signal(
        self,
        message_name: str,
        signal_name: str,
        frame_bytes: List[int]
    ) -> float:
        """Extract a signal value from a CAN frame

        Uses the verified Agda signal extraction logic.

        Args:
            message_name: Name of the CAN message
            signal_name: Name of the signal to extract
            frame_bytes: 8-byte frame data as list of integers (0-255)

        Returns:
            Extracted signal value (scaled with factor/offset)

        Raises:
            ValueError: If frame_bytes is not exactly 8 bytes
            RuntimeError: If extraction fails
        """
        if len(frame_bytes) != 8:
            raise ValueError(f"Frame must be exactly 8 bytes, got {len(frame_bytes)}")

        if not all(0 <= b <= 255 for b in frame_bytes):
            raise ValueError("Frame bytes must be in range 0-255")

        # Format frame bytes as hex string: "0x12 0x34 ..."
        frame_hex = " ".join(f"0x{b:02X}" for b in frame_bytes)

        # Build command YAML manually with multiline literal format
        # Use original YAML to preserve hex formatting (0x100 vs 256)
        command_yaml = f'''command: "ExtractSignal"
message: "{message_name}"
signal: "{signal_name}"
frame: {frame_hex}
dbc_yaml: |
'''
        for line in self.dbc_yaml.splitlines():
            if line.strip():
                command_yaml += f'  {line}\n'
            else:
                command_yaml += '\n'

        # Call binary
        response = _call_binary(command_yaml)

        # Check response status
        if not response.get('success'):
            error_msg = response.get('message', 'Unknown error')
            raise RuntimeError(f"Failed to extract signal: {error_msg}")

        # Parse the value (returned as rational string like "3/2")
        value_str = response.get('value', '0/1')
        return _parse_rational(value_str)

    def inject_signal(
        self,
        message_name: str,
        signal_name: str,
        value: float,
        frame_bytes: List[int]
    ) -> List[int]:
        """Inject a signal value into a CAN frame

        Uses the verified Agda signal injection logic.

        Args:
            message_name: Name of the CAN message
            signal_name: Name of the signal to inject
            value: Signal value to inject (will be scaled with factor/offset)
            frame_bytes: 8-byte frame data as list of integers (0-255)

        Returns:
            Modified frame bytes as list of integers

        Raises:
            ValueError: If frame_bytes is not exactly 8 bytes
            RuntimeError: If injection fails
        """
        if len(frame_bytes) != 8:
            raise ValueError(f"Frame must be exactly 8 bytes, got {len(frame_bytes)}")

        if not all(0 <= b <= 255 for b in frame_bytes):
            raise ValueError("Frame bytes must be in range 0-255")

        # Format frame bytes as hex string
        frame_hex = " ".join(f"0x{b:02X}" for b in frame_bytes)

        # Build command YAML manually with multiline literal format
        # Use original YAML to preserve hex formatting (0x100 vs 256)
        command_yaml = f'''command: "InjectSignal"
message: "{message_name}"
signal: "{signal_name}"
value: {value}
frame: {frame_hex}
dbc_yaml: |
'''
        for line in self.dbc_yaml.splitlines():
            if line.strip():
                command_yaml += f'  {line}\n'
            else:
                command_yaml += '\n'

        # Call binary
        response = _call_binary(command_yaml)

        # Check response status
        if not response.get('success'):
            error_msg = response.get('message', 'Unknown error')
            raise RuntimeError(f"Failed to inject signal: {error_msg}")

        # Parse the frame hex string back to bytes
        frame_result = response.get('frame', '')
        return _parse_frame_hex(frame_result)

    def check_ltl(
        self,
        trace: List[Dict[str, Any]],
        property_yaml: str
    ) -> bool:
        """Check an LTL property on a CAN trace

        Uses the verified Agda LTL model checker.

        Args:
            trace: List of trace frames, each with:
                   - timestamp: int (microseconds)
                   - id: int (CAN ID as hex, e.g., 0x100)
                   - dlc: int (data length)
                   - data: List[int] (8 bytes)
            property_yaml: LTL property in YAML format, e.g.:
                   type: always
                   formula:
                     type: compare
                     signal: VehicleSpeed
                     op: LT
                     value: 300

        Returns:
            True if property holds on trace, False if violated

        Raises:
            RuntimeError: If checking fails
        """
        # Format trace as YAML with frames: key
        trace_lines = ['frames:']
        for frame in trace:
            trace_lines.append(f"  - timestamp: {frame['timestamp']}")
            # Format ID as hex
            frame_id = frame['id']
            if isinstance(frame_id, int):
                trace_lines.append(f"    id: 0x{frame_id:X}")
            else:
                trace_lines.append(f"    id: {frame_id}")
            trace_lines.append(f"    dlc: {frame.get('dlc', 8)}")
            # Format data as hex array
            data = frame['data']
            data_hex = ", ".join(f"0x{b:02X}" for b in data)
            trace_lines.append(f"    data: [{data_hex}]")
        trace_yaml = '\n'.join(trace_lines)

        # Build command YAML with --- separators
        command_yaml = 'command: "CheckLTL"\ndbc_yaml: |\n'
        for line in self.dbc_yaml.splitlines():
            if line.strip():
                command_yaml += f'  {line}\n'
            else:
                command_yaml += '\n'
        command_yaml += '---\ntrace_yaml: |\n'
        for line in trace_yaml.splitlines():
            if line.strip():
                command_yaml += f'  {line}\n'
            else:
                command_yaml += '\n'
        command_yaml += '---\nproperty_yaml: |\n'
        for line in property_yaml.splitlines():
            if line.strip():
                command_yaml += f'  {line}\n'
            else:
                command_yaml += '\n'

        # Call binary
        response = _call_binary(command_yaml)

        # Check response status
        if not response.get('success'):
            error_msg = response.get('message', 'Unknown error')
            raise RuntimeError(f"Failed to check property: {error_msg}")

        return response.get('property_holds', False)

    def signal(self, signal_name: str) -> 'SignalRef':
        """Create a reference to a signal for use in LTL formulas

        Note: This is for Phase 2 (LTL checking). Phase 1 focuses on
        extraction/injection.

        Args:
            signal_name: Name of the signal

        Returns:
            SignalRef that can be used in comparisons
        """
        return SignalRef(signal_name)

    def decode(self, frame_id: int, data: bytes) -> Dict[str, float]:
        """Decode all signals in a CAN frame

        Note: This is a convenience wrapper around extract_signal.
        For Phase 1, we focus on single-signal extraction.
        Full frame decoding will be optimized in Phase 2.

        Args:
            frame_id: CAN frame identifier
            data: Frame data bytes

        Returns:
            Dictionary mapping signal names to values

        Raises:
            NotImplementedError: Phase 2 feature
        """
        # TODO Phase 2: Implement using DBC/Semantics.agda:decodeFrame
        raise NotImplementedError(
            "Full frame decoding not yet implemented. "
            "Use extract_signal() for individual signals in Phase 1."
        )


class SignalRef:
    """Reference to a CAN signal for use in LTL formulas (Phase 2)"""

    def __init__(self, name: str):
        self.name = name

    def __gt__(self, other: float) -> 'Comparison':
        return Comparison(self, 'GT', other)

    def __lt__(self, other: float) -> 'Comparison':
        return Comparison(self, 'LT', other)

    def __ge__(self, other: float) -> 'Comparison':
        return Comparison(self, 'GE', other)

    def __le__(self, other: float) -> 'Comparison':
        return Comparison(self, 'LE', other)

    def __eq__(self, other: float) -> 'Comparison':  # type: ignore
        return Comparison(self, 'EQ', other)

    def __ne__(self, other: float) -> 'Comparison':  # type: ignore
        return Comparison(self, 'NE', other)


class Comparison:
    """Signal comparison expression (Phase 2 - LTL)"""

    def __init__(self, signal: SignalRef, op: str, value: float):
        self.signal = signal
        self.op = op
        self.value = value

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization"""
        return {
            'type': 'comparison',
            'signal': self.signal.name,
            'op': self.op,
            'value': self.value
        }


# Helper functions

def _parse_rational(rational_str: str) -> float:
    """Parse Agda rational output (format: "numerator/denominator")

    Args:
        rational_str: Rational in format "3/2" or "1/4"

    Returns:
        Floating point value

    Examples:
        >>> _parse_rational("3/2")
        1.5
        >>> _parse_rational("1/4")
        0.25
    """
    try:
        if '/' in rational_str:
            parts = rational_str.split('/')
            numerator = int(parts[0].strip())
            denominator = int(parts[1].strip())
            if denominator == 0:
                raise ValueError("Division by zero in rational")
            return numerator / denominator
        else:
            # Handle case where it's just an integer
            return float(rational_str.strip())
    except (ValueError, IndexError) as e:
        raise ValueError(f"Invalid rational format: {rational_str}") from e


def _parse_frame_hex(hex_str: str) -> List[int]:
    """Parse frame hex string back to list of bytes

    Args:
        hex_str: Frame in format "0x12 0x34 0x56 ..."

    Returns:
        List of 8 integers (0-255)

    Examples:
        >>> _parse_frame_hex("0x12 0x34 0x56 0x78 0x9A 0xBC 0xDE 0xF0")
        [18, 52, 86, 120, 154, 188, 222, 240]
    """
    try:
        parts = hex_str.strip().split()
        if len(parts) != 8:
            raise ValueError(f"Expected 8 bytes, got {len(parts)}")

        bytes_list = []
        for part in parts:
            # Remove "0x" prefix and parse as hex
            if part.startswith('0x') or part.startswith('0X'):
                part = part[2:]
            byte_val = int(part, 16)
            if not (0 <= byte_val <= 255):
                raise ValueError(f"Byte value out of range: {byte_val}")
            bytes_list.append(byte_val)

        return bytes_list
    except (ValueError, IndexError) as e:
        raise ValueError(f"Invalid frame hex format: {hex_str}") from e
