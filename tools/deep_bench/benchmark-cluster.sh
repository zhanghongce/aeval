#!/usr/bin/env bash

REGION="us-east-1"
cd terraform || exit 1
terraform apply -var-file=~/.tfvars -var aws_region=$REGION || exit 1
cd ..

echo ""
echo "  Wait for the cluster to be up and running (not initializing)."
echo "  Then hit Enter to continue."
echo ""
read

# Get IP addresses
cd terraform || exit 1
terraform refresh -var-file=~/.tfvars -var aws_region=$REGION || exit 1
SFR_ID=`jq -r ".modules[0].resources.\"aws_spot_fleet_request.fleet_req\".primary.id" terraform.tfstate`
INSTANCE_IDS=`aws ec2 describe-spot-fleet-instances --spot-fleet-request-id $SFR_ID | jq -r ".ActiveInstances[].InstanceId" | awk '{$1=$1};1'`
HOSTS=`aws ec2 describe-instances --instance-ids $INSTANCE_IDS | jq -r '.Reservations[0].Instances[].PublicIpAddress' | sed -e 's/^/1\/ubuntu@/' | xargs echo -n | tr ' ' ','`
echo $HOSTS
cd ..

# Disable StrictHostKeyChecking temporarily. (So hacky.)
touch ~/.ssh/config
cp ~/.ssh/config ~/.ssh/config.backup
(echo 'Host *'; echo StrictHostKeyChecking no) >> ~/.ssh/config

find ../../bench_horn/*.smt2 -exec basename {} .smt2 \; | BENCH_MPIRUN=/usr/bin/mpirun parallel \
  --resume-failed \
  --joblog ./clusterjobs.log \
  --return "out-{1}-{2}.tar.gz" \
  --cleanup \
  -a - \
  --env BENCH_MPIRUN \
  --sshlogin $HOSTS \
  "rm -rf out && " \
  "mkdir out && " \
  "cd /home/ubuntu/aeval/tools/deep_bench && " \
  "./benchmark.py -v -i 10 --logdir /home/ubuntu/out/benchlogs -o /home/ubuntu/out/ --hyper {2} /home/ubuntu/aeval/bench_horn/{1}.smt2 &> /home/ubuntu/out/std.log ; " \
  "cd /home/ubuntu ; " \
  "tar -zcf out-{1}-{2}.tar.gz out/ ;" \
  ::: 1,agg_on 1,agg_off 4,agg_on 4,agg_off

# Remove the disabling of StrictHostKeyChecking
mv ~/.ssh/config.backup ~/.ssh/config
