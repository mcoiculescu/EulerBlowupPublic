from graphlib import TopologicalSorter
from pathlib import Path
import json
import os
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parent
manifest = json.loads((root / "lake-manifest.json").read_text())
packages = root / manifest["packagesDir"]
dependencies = []
for package in manifest["packages"]:
    checkout = packages / package["name"]
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
    if commit != package["rev"]:
        raise SystemExit(f"{package['name']} checkout does not match lake-manifest.json")
    dependencies.append(checkout / ".lake" / "build" / "lib" / "lean")

imports = re.compile(r"^(?:public )?import (TorusEuler(?:\.[\w]+)*)\s*$", re.MULTILINE)
graph = {}
sources = {}
pending = ["TorusEuler"]
while pending:
    module = pending.pop()
    if module in graph:
        continue
    source = root / Path(*module.split(".")).with_suffix(".lean")
    if not source.is_file():
        raise SystemExit(f"Missing project module: {module}")
    sources[source.relative_to(root)] = source.read_text()
    graph[module] = imports.findall(sources[source.relative_to(root)])
    pending.extend(graph[module])
for filename in ("lean-toolchain", "Verify.lean"):
    sources[Path(filename)] = (root / filename).read_text()

with tempfile.TemporaryDirectory(prefix="torus-lean-") as directory:
    snapshot = Path(directory) / "src"
    build = Path(directory) / "build"
    for path, contents in sources.items():
        copied = snapshot / path
        copied.parent.mkdir(parents=True, exist_ok=True)
        copied.write_text(contents)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [build, *dependencies])))
    lean = ["lean", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DwarningAsError=true"]
    for module in TopologicalSorter(graph).static_order():
        source = Path(*module.split(".")).with_suffix(".lean")
        compiled = (build / source).with_suffix(".olean")
        compiled.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            [*lean, "-o", str(compiled), str(source)],
            cwd=snapshot, env=env, check=True,
        )
    subprocess.run([*lean, "Verify.lean"], cwd=snapshot, env=env, check=True)
