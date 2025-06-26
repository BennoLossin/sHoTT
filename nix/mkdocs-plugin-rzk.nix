{
  python3Packages,
  fetchPypi,
  mkdocs,
}:
python3Packages.buildPythonPackage rec {
  pname = "mkdocs-plugin-rzk";
  version = "0.1.4";
  pyproject = true;

  src = fetchPypi {
    inherit pname version;
    hash = "sha256-2bXIzsvumSWx0X5bTqA7HF76j4C2kaxvp/49tagWiq0=";
  };

  buildInputs = [
    python3Packages.setuptools
    python3Packages.wheel
    python3Packages.materialx
    mkdocs
  ];
}
