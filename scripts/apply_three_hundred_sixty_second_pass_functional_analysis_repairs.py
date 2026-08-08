from __future__ import annotations
import base64
from hashlib import sha256
from pathlib import Path
import subprocess
import zlib
ROOT=Path(__file__).resolve().parents[1]
TARGET=ROOT/"PrimalitySheafVerification"/"Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256="5ab144401a2798e13e52c9cd7a359ace82a7f8c97d28351a4a48ae14d5e1f19e"
EXPECTED_OUTPUT_SHA256="b8142deb44c984965dae3f047675242a61d373f921ad1e5c4e91e6004f5b86b2"
PATCH_ZLIB_BASE64="eNqlVs1u20YQvvMp5lYJFKlIdWvHgAAbrp0GSGo3CtpDYEgrakSuTe4yu0vJKtBLEPQBemhfoO/QnvsoepLOLklRsh1bdg8EuOT8f9/MbBAEwLoXimcs5WY5TJDNfkLFZzxihkvRfSuj6/7orBCRPbL0mJ6l5jpMkQnP932YPF/96AiC/v7XBy87/ZfgV28v4OjIAwDFuMYpHA6qtxMp1ZQLZhBaAnzota1UKheoKjHkYoo3OD2OTMHSN+WfDTXhgRd0KeP3CQJzQqU+FzFEjZycwbg5anLn99rjDhjFhM6lMuRPinTpBSxSUmsw1p7iJsnQ8Aj4FIWhcsDYaQa9gRiHEHQ9v3auiyhCraUKqpDvjYMLZ3mKMy54Wb90CXhDoXu+YSpGAzpnEYYAr40G/Fg4GGBBoThVxRZbUW8aJ/mbXNoST5ZkzkWllCzE1IYRK5YnJJ/llJiWLhKpMCOT9KboyAQpAgOzzDFKmdaBRqEpzjl6fsS0sXWckLnUpscFMgUZy7WrBAgprPHCsEnqUtyMc1iX5y6GBP0hrD7/1YZDCz8lLuaoNJ4adsapkBcJ03hCkdYkgdVvv68+/flh9fnTpRc4FThXE24u0JAipfY9TyeoDAhLIqoFCSVsjpC8p8zIzYNKpRcIrKfB44aBSipiBb3yIDOMmX11oFYeV3/8U/5tfbdG/lzgUE5kivOwSfOVxeiEqpiilQm3Oeuyb4dVg3j+Y6lbiae10CazHmgnXjaIRqISnYnCljJTL1h3wb1qRUlNp5snNDQisu9o+YVeeorztUWi6v0uryQXZsPfugF24ukIP96l6m4MFzCoKfc4HA2zWJ5Tcm9cn71leYg3xn6mJJSEopFYY2+bZOimh5ENiUZcXGHkmvghlcp6+X+YSWkcEYkFPyOPE2Mla6FZIegNfqkpuFNWbgPMUqIblEATkAoXNGQNik2Ayec1ix3QNPtQuRlpAZSKxyRScabaNXv9vU6vZ3fNXu+bzkG1aqq46oXTfPpfPbhpBpqGLN3UEG9tsF0J8utt2O8N8sdCGk6bqGryxoKukfn3b1fj22/lMGrtTHTRDvUyy2p8n52Sm0AN5qc02JduhTUtXq6lOTGUDhNMaZhSg0sHeIyiIPo3w8K1sAcyJ1aYWtk1c0mG/YODigz7+992ei822EB7WdCWo6UBrbR/9+oB8za07txLBBTtChqol8g7K2Q/1mHZDzSkXilE8bq6KZy71oLEfYQC5o3+iRRXVt3tjWMVQ0vT6n9HFk7F1AbYrnw0e8uqfNUsruenMmhYulUQi9+ZkplFdEvHmtrysVERZ0pzGhLu8gQf6DIwEhh3YCOhkeNzp4x5RDlfjSy1Lmk028HuUmsS/QHjrdLQOSSLVQUcnRaNn5Kftyw/tSZftPK0mlwCM1U2/k7ZeLeKRz9sUuvCWGHXhFXzHFPzsNj+sq1hFrLe0JElWskzXWQarhHzckdGEmd0cbcjA8a9bn8cev8BK2QboA=="
def file_sha256(path: Path)->str: return sha256(path.read_bytes()).hexdigest()
def main()->int:
    before=file_sha256(TARGET); print(f"input_sha256={before}")
    if before==EXPECTED_OUTPUT_SHA256: print("[pass362] already applied"); return 0
    if before!=EXPECTED_INPUT_SHA256: raise RuntimeError(f"unexpected pass362 input sha256: {before}; expected {EXPECTED_INPUT_SHA256}")
    patch=zlib.decompress(base64.b64decode(PATCH_ZLIB_BASE64))
    subprocess.run(["git","apply","--whitespace=nowarn","-"],cwd=ROOT,input=patch,check=True)
    after=file_sha256(TARGET); print(f"output_sha256={after}")
    if after!=EXPECTED_OUTPUT_SHA256: raise RuntimeError(f"unexpected pass362 output sha256: {after}; expected {EXPECTED_OUTPUT_SHA256}")
    print("[pass362] FunctionalAnalysis successor coordinate and Green conjugation roots repaired")
    return 0
if __name__=="__main__": raise SystemExit(main())
