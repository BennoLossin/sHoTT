{
  mkShell,
  python3Packages,
  mkdocs,
  mkdocs-plugin-rzk,
  pygments-rzk,
  materialx,
  rzk,
}:
mkShell {
  name = "rzk";

  packages = [
    python3Packages.mkdocs-material
    python3Packages.python-markdown-math
    python3Packages.materialx
    materialx
    mkdocs-plugin-rzk
    pygments-rzk
    mkdocs
    rzk
  ];
}
