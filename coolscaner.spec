# -*- mode: python ; coding: utf-8 -*-


a = Analysis(
    ['coolscaner.py'],
    pathex=[],
    binaries=[],
    datas=[('google-service-account.json', '.'), ('check_in_system.db', '.')],
    hiddenimports=['pypdf'],
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
    name='coolscaner',
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
    name='coolscaner',
)
app = BUNDLE(
    coll,
    name='coolscaner.app',
    icon=None,
    bundle_identifier=None,
)
