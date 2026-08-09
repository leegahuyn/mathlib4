from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / 'PrimalitySheafVerification' / 'Mock2_FunctionalAnalysis.lean'
EXPECTED_INPUT_SHA256 = 'be21e702089c0de8f9a5a4e5c1af8eb0963869cf93271c469d0516e55caa6fd5'
EXPECTED_OUTPUT_SHA256 = 'c980501c4a7f0f6582c5d67ec7fa08c7af37ffd6aa3335a3724928f94c2de03f'
PAYLOAD = '''eNrlVs1u20YQfpWBL6FamtAfJcVACgSq7RiwHTd2T7JArMiltcj+0MtdKfIpCIICvfURgqBv0PfoQ+hJOkuRFGXYiQtfCvQy4M/MNzPf7MzsZNJ5OWz3fJSdrj/Zk0rGSmTWkBmnkNAUYqV0wiQxNAdPwgGsP//ZgoNXMFtdyz1/D4BTc4LfXyfJWAlxrJXNwDuRC6pzemjIEftAk4s5yelYaQrSGZeWAOwRtR0wuevoTCUWg1t//vRsNyVU5YB+ILGBX6wyjErzhvEZ1Wa8JSAQ72tIj3e3f5w7TxOW0+TeR66WVN/7ihjTqT/ptgdh6G/kBDHnZEFh/jo2TCHPtSOAv/+C9cevcAevwPPw5QAuT72uX1Sitfm1WxGAnImMwOSYCEGulqpK6ZgqQY1eBTfljyt1edp9Rwmfgs2ZvGl49Z5uHOXCchfmXasE0EuYrH/7o0pn2kh5UKQ8KlJuVuaCZFS/1TNmjrAKSpcRwXysFpV5J+x1fCd7hbnzEiuZGyKxTJhxbMY2z64I45Fxgt5Gd1QrH6TSonisI+n2hm1/I/8v5GOynSLlXkn+SX7yAP3IN9EMKfWheD+z3LCMM/pgSXqdHvKIsl+CIuxjTYnz40fotGA5x54ogzXqyEqwzW59zD4oOgwkeDFWeWyNStO3GDXB0wLn+N22YL9B4oNaVQzed73Yik9BsogkyQuMcvFAqUFJvoJJqTWt/5EZ5Q0EV6YXEBepfgPCqfngZJTb2bRB88jR3O8+ieb959BczKzn07z/bZorL/8xmsOuozncnOaGUXEqxnWqbjvhlsRkfbhgAWJEJMv4qoE07Duk4eA+UpH4v0HqhQ6pFw6eHFPD1k05lN0nR7G1HblZjfJlYVssx+36CzK1RJmwxfrTR7wlSMOkVTaPioHcHGW/Zngs3hCeXnAiadBQZcKla1YZjcR7iFpNqxSPKw7dn+D83E25QNKIpWmA8d8FTET46sY5juCo3qf9YQeJQhnWPeLlcwyzhEAfznYDkKk8cLeI379AG1KtRMM5fMfp1mHYdg7DTukwnhN5Q8G6jA9tzFlCiTyjJLd1IxZRxXOVU1nNeOzMhAgc8oT/rARhMoiJ1jhv4fp6J6pq9mOfyfFGpYV7qV0rbS4wG/RSIUowg0ihRSQt59FubHUmI7z+Odnf1hrOqDjNAkJxjW7rfsS4oTo4XGC8lnC+ClQapUrjI9Q1K/quAg4L4EFdE53ybaU99CCcH7htBbjI9dZwMPI3clITUPJLxMztxEtUf0czTXPHnWELN7VvYQk/4ABZlsRMp9N/AERRh2c='''


def digest(text: str) -> str:
    return sha256(text.encode('utf-8')).hexdigest()


def main() -> None:
    text = TARGET.read_text(encoding='utf-8')
    input_sha = digest(text)
    print(f'input_sha256={input_sha}')
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print('[pass347-v2] already applied')
        return
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f'unexpected pass347-v2 input sha256: {input_sha}; '
            f'expected {EXPECTED_INPUT_SHA256}'
        )

    lines = text.splitlines(keepends=True)
    operations = json.loads(decompress(b64decode(PAYLOAD)).decode('utf-8'))
    print(f'line_operations={len(operations)}')
    for start, stop, replacement in reversed(operations):
        lines[start:stop] = replacement
    output = ''.join(lines)
    output_sha = digest(output)
    print(f'output_sha256={output_sha}')
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f'unexpected pass347-v2 output sha256: {output_sha}; '
            f'expected {EXPECTED_OUTPUT_SHA256}'
        )
    TARGET.write_text(output, encoding='utf-8')
    print('[pass347-v2] deterministic line-index frontier repairs applied')


if __name__ == '__main__':
    main()
