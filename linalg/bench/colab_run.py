"""Run linalg + GPU benchmarks on a Colab Xeon + NVIDIA GPU VM.

Upload linalg.bend, bench_suite.bend, bench_gpu.bend, bench_numpy.py to
/content/linalg/ first, then execute this script via:
    colab exec -s <session> -f linalg/bench/colab_run.py
"""
import os
import shutil
import subprocess
import tarfile
import time

os.makedirs("/content/linalg/bench/out", exist_ok=True)
if os.path.exists("/content/linalg_bench.tar.gz"):
    with tarfile.open("/content/linalg_bench.tar.gz", "r:gz") as tf:
        tf.extractall("/content/linalg")


def run(cmd, cwd=None, check=True):
    print(f"$ {cmd}", flush=True)
    p = subprocess.Popen(cmd, shell=True, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    for line in p.stdout:
        print(line, end="", flush=True)
    rc = p.wait()
    if check and rc != 0:
        raise RuntimeError(f"Command failed ({rc}): {cmd}")
    return rc


print("=== HARDWARE ===", flush=True)
run("lscpu | grep -E 'Model name|CPU\\(s\\):|Thread|Core|Socket'", check=False)
run("free -h | head -n 2", check=False)
run("nvidia-smi --query-gpu=name,memory.total,driver_version,compute_cap --format=csv", check=False)
run("nvcc --version | tail -n 2", check=False)

has_gpu = shutil.which("nvidia-smi") is not None

if has_gpu and not shutil.which("clang-19"):
    print("\n=== INSTALLING CLANG 19 FOR CUDA GPU ===", flush=True)
    run("curl -fsSL https://apt.llvm.org/llvm.sh | bash -s 19")
elif not shutil.which("clang"):
    print("\n=== INSTALLING CLANG ===", flush=True)
    run("apt-get update -qq && apt-get install -y -qq clang")

bend = os.path.expanduser("~/.bend/bin/bend")
if not os.path.exists(bend):
    print("\n=== INSTALLING BEND ===", flush=True)
    run("curl -fsSL https://bend-lang.com/install.sh | sh")

os.environ["PATH"] = os.path.expanduser("~/.bend/bin") + ":" + os.environ["PATH"]
run(f"{bend} version")

print("\n=== BUILDING BEND BENCHMARKS ===", flush=True)
run(f"{bend} bench_suite.bend -o out/bench_suite", cwd="/content/linalg/bench")
if has_gpu:
    run(f"{bend} bench_gpu.bend -o out/bench_gpu", cwd="/content/linalg/bench")

print("\n=== CPU: BEND linalg.bend (1t) ===", flush=True)
run("./out/bench_suite +RTS --threads 1 -RTS", cwd="/content/linalg/bench")

print("\n=== CPU: BEND linalg.bend (all threads) ===", flush=True)
run("./out/bench_suite", cwd="/content/linalg/bench")

print("\n=== CPU: NUMPY / SCIPY ===", flush=True)
run("python3 bench_numpy.py", cwd="/content/linalg/bench")

if has_gpu:
    print("\n=== CUDA GPU + CPU: BEND bench_gpu ===", flush=True)
    run("./out/bench_gpu", cwd="/content/linalg/bench")

    print("\n=== CPU 1t: BEND bench_gpu (--gpu off --threads 1) ===", flush=True)
    run("./out/bench_gpu +RTS --gpu off --threads 1 -RTS", cwd="/content/linalg/bench")

print("\n=== PYTORCH CUDA GPU BASELINE ===", flush=True)
try:
    import torch
    if torch.cuda.is_available():
        dev = torch.device("cuda")
        print("torch:", torch.__version__, "device:", torch.cuda.get_device_name(0), flush=True)

        def tbench(fn, reps=50):
            fn()
            torch.cuda.synchronize()
            t0 = time.perf_counter()
            for _ in range(reps):
                fn()
            torch.cuda.synchronize()
            return (time.perf_counter() - t0) * 1000.0 / reps

        torch.manual_seed(42)
        B = torch.randn(1000, 50, device=dev, dtype=torch.float32)
        G = torch.randn(50, 50, device=dev, dtype=torch.float32)
        Omega = G.T @ G + 10.0 * torch.eye(50, device=dev, dtype=torch.float32)
        x50 = torch.randn(50, device=dev, dtype=torch.float32)
        y1000 = torch.randn(1000, device=dev, dtype=torch.float32)
        A500 = torch.randn(500, 30, device=dev, dtype=torch.float32)
        R16k = torch.randn(16384, 64, device=dev, dtype=torch.float32)
        X64 = torch.randn(64, device=dev, dtype=torch.float32)
        B64x16 = torch.randn(64, 16, device=dev, dtype=torch.float32)

        for name, fn, reps in [
            ("matvec_1000x50", lambda: B @ x50, 200),
            ("matmul_1000x50x50", lambda: B @ Omega, 200),
            ("gram_1000x50", lambda: B.T @ B, 200),
            ("cholesky_50x50", lambda: torch.linalg.cholesky(Omega), 200),
            ("qr_thin_1000x50", lambda: torch.linalg.qr(B, mode="reduced"), 50),
            ("lstsq_1000x50", lambda: torch.linalg.lstsq(B, y1000), 50),
            ("sym_eigen_50x50", lambda: torch.linalg.eigh(Omega), 50),
            ("svd_thin_500x30", lambda: torch.linalg.svd(A500, full_matrices=False), 50),
            ("matvec_16384x64", lambda: R16k @ X64, 200),
            ("matmul_16384x64x16", lambda: R16k @ B64x16, 200),
        ]:
            ms = tbench(fn, reps)
            print(f"{name:<26} {ms:>10.4f} ms", flush=True)
    else:
        print("CUDA not available in torch", flush=True)
except Exception as e:
    print("PyTorch baseline skipped:", e, flush=True)
