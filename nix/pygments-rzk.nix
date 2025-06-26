{
  python3Packages,
  fetchPypi,
}:
python3Packages.buildPythonPackage rec {
  pname = "pygments-rzk";
  version = "0.1.4";
  pyproject = true;

  src = fetchPypi {
    inherit pname version;
    hash = "sha256-7xC22yJByk3lXTjncKqWPAU56TzHdSMM04q/F3Suc6U=";
  };

  buildInputs = with python3Packages; [setuptools wheel pygments];
}
