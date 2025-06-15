GetSystem := proc()
    local sys;
    sys := kernelopts(system);
    if StringTools:-Has(sys, "APPLE") then
        return "macOS";
    elif StringTools:-Has(sys, "LINUX") then
        return "Linux";
    else
        return "Windows";
    fi;
end proc:

GetLocalHostName := proc()
    local sys;
    sys := GetSystem();
    if sys = "macOS" then
        return StringTools:-Trim(ssystem("scutil --get LocalHostName")[2]);
    else
        return Sockets:-GetHostName();
    fi;
end proc:

GetUserName := proc()
    StringTools:-Trim(ssystem("whoami")[2])
end proc:

if StringTools:-Has(GetLocalHostName(), "Weijia") then
    mspath := "nix run github:NixOS/nixpkgs/nixos-unstable#msolve --":
elif GetSystem() = "Linux" and StringTools:-Has(GetUserName(), "weijia") then
    mspath := "/home/weijia/msolve/msolve":
else
    mspath := "":
fi:
