#!/usr/bin/env bash
./upload
sshpass -e ssh root@$(cat server) /tmp/run