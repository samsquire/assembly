{ pkgs }: {
	deps = [
   pkgs.sshpass
   pkgs.hdf5-mpi
   pkgs.wget
   pkgs.openssh
   pkgs.vim
		pkgs.clang_12
		pkgs.ccls
		pkgs.gdb
		pkgs.gnumake
		pkgs.liburing
		pkgs.openssh
	];
}
