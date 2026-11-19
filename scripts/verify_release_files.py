"""Verify the distributed files against SHA256SUMS from any working directory."""
from hashlib import sha256
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    count = 0
    for line in (root / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        expected, name = line.split("  ", 1)
        path = (root / name).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise SystemExit(f"Missing or invalid release path: {name}")
        if sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit(f"Checksum mismatch: {name}")
        count += 1
    print(f"Verified {count} distributed files.")


if __name__ == "__main__":
    main()
