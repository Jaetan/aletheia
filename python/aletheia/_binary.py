"""Binary location and subprocess management"""

import subprocess
import json
import yaml
from pathlib import Path
from typing import Dict, Any


def get_binary_path() -> Path:
    """Locate the Aletheia binary
    
    Returns:
        Path to the binary
        
    Raises:
        FileNotFoundError: If binary not found
    """
    module_dir = Path(__file__).parent
    repo_root = module_dir.parent.parent
    binary = repo_root / "build" / "aletheia"
    
    if not binary.exists():
        raise FileNotFoundError(
            f"Aletheia binary not found at {binary}. "
            f"Please build it first with: cabal run shake -- build"
        )
    
    return binary


def call_aletheia_binary(command: Dict[str, Any]) -> Dict[str, Any]:
    """Call the Aletheia binary with a command
    
    Args:
        command: Command dictionary to send
        
    Returns:
        Response dictionary from binary
        
    Raises:
        RuntimeError: If binary execution fails
    """
    binary = get_binary_path()
    
    command_yaml = yaml.dump(command)
    
    try:
        result = subprocess.run(
            [str(binary)],
            input=command_yaml.encode('utf-8'),
            capture_output=True,
            check=True,
            timeout=60
        )
        
        response_yaml = result.stdout.decode('utf-8')
        response = yaml.safe_load(response_yaml)
        
        return response
        
    except subprocess.CalledProcessError as e:
        stderr = e.stderr.decode('utf-8') if e.stderr else 'No error output'
        raise RuntimeError(
            f"Aletheia binary failed with exit code {e.returncode}: {stderr}"
        )
    except subprocess.TimeoutExpired:
        raise RuntimeError("Aletheia binary timed out after 60 seconds")
    except yaml.YAMLError as e:
        raise RuntimeError(f"Failed to parse binary response: {e}")
