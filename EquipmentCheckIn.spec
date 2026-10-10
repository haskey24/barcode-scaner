# -*- mode: python ; coding: utf-8 -*-


a = Analysis(
    ['coolscaner.py'],
    pathex=[],
    binaries=[],
    datas=[('google-service-account.json', '.')],
    hiddenimports=['pypdf', 'gspread', 'keyring.backends.macOS'],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name='EquipmentCheckIn',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
)
coll = COLLECT(
    exe,
    a.binaries,
    a.datas,
    strip=False,
    upx=True,
    upx_exclude=[],
    name='EquipmentCheckIn',
)
app = BUNDLE(
    coll,
    name='EquipmentCheckIn.app',
    icon=None,
    bundle_identifier=None,
)
