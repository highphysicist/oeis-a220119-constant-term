# Paste this as a NEW cell in the SAME Colab runtime after verification succeeds.
from google.colab import files
from zipfile import ZipFile
from io import BytesIO

uploaded = files.upload()  # Upload the complete updated A220119_Lean_Colab.zip.
assert len(uploaded) == 1, 'Upload exactly one complete asset ZIP'
asset_bytes = next(iter(uploaded.values()))
with ZipFile(BytesIO(asset_bytes)) as archive:
    publisher = archive.read('A220119_Lean/publish_github.py')
exec(compile(publisher, 'publish_github.py', 'exec'),
     {'__name__': '__main__', 'ASSET_BYTES': asset_bytes})
