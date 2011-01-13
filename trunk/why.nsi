;
; why.nsi
; Created by Aurélien OUDOT
; Modified by Claude Marché
;

Name "Why"
Icon "icons\install.ico"
OutFile "why-${VERSION}-install.exe"

LicenseText "This application will install the Why platform"
LicenseData "LICENSE"
ComponentText "Why platform installation"
DirText "Destination Folder"

InstallDir "$PROGRAMFILES\Why"
UninstallText "Do you really want to delete Why from your system ?"
UninstallIcon "icons\uninstall.ico"

; ================================================================

Section "Program"
        SectionIn 1 2
	setOutPath "$INSTDIR\bin"
	File "bin\*"
	setOutPath "$INSTDIR\lib"
	File /r "lib\*"
SectionEnd

Section -PostInstall
        WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\Why" "DisplayName" "Why (uninstall)"
        WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\Why" "UninstallString" '"$INSTDIR\why_uninstall.exe"'
        writeUninstaller "why_uninstall.exe"
        WriteRegStr HKLM "Software\Why" "Directory" '"$INSTDIR"'
SectionEnd

Section "ShortCut"
        SectionIn 2
        setOutPath "$SMPROGRAMS\Why"
        CreateShortCut "$SMPROGRAMS\Why\krakatoa.lnk" "$INSTDIR\bin\krakatoa.exe"
        CreateShortCut "$SMPROGRAMS\Why\caduceus.lnk" "$INSTDIR\bin\caduceus.exe"
        CreateShortCut "$SMPROGRAMS\Why\why-cpulimit.lnk" "$INSTDIR\bin\why-cpulimit.exe"
        CreateShortCut "$SMPROGRAMS\Why\why-dp.lnk" "$INSTDIR\bin\why-dp.exe"
        CreateShortCut "$SMPROGRAMS\Why\jessie.lnk" "$INSTDIR\bin\jessie.exe"
        CreateShortCut "$SMPROGRAMS\Why\why-stat.lnk" "$INSTDIR\bin\why-stat.exe"
        CreateShortCut "$SMPROGRAMS\Why\why-obfuscator.lnk" "$INSTDIR\bin\why-obfuscator.exe"
        CreateShortCut "$SMPROGRAMS\Why\why.lnk" "$INSTDIR\bin\why.exe"
        CreateShortCut "$SMPROGRAMS\Why\why2html.lnk" "$INSTDIR\bin\why2html.exe"
        CreateShortCut "$SMPROGRAMS\Why\simplify2why.lnk" "$INSTDIR\bin\simplify2why.exe"
        CreateShortCut "$SMPROGRAMS\Why\rv_merge.lnk" "$INSTDIR\bin\rv_merge.exe"
        IfFileExists "$INSTDIR\bin\gwhy.exe" 0 +2
             CreateShortCut "$SMPROGRAMS\Why\gwhy.lnk" "$INSTDIR\bin\gwhy.exe"
        IfFileExists "$INSTDIR\bin\gwhy-bin.exe" 0 +2
             CreateShortCut "$SMPROGRAMS\Why\gwhy-bin.lnk" "$INSTDIR\bin\gwhy-bin.exe"
        CreateShortCut "$SMPROGRAMS\Why\why_uninstall.lnk" "$INSTDIR\why_uninstall.exe"
SectionEnd

Section "Uninstall"
        DeleteRegKey HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\Why"
        DeleteRegKey HKLM "Software\Why"
        RMDir /r "$INSTDIR"
        RMDir /r "$SMPROGRAMS\Why"
SectionEnd

