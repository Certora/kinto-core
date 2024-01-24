mutateFileA="KintoWallet"
mutateFileB=".sol"
imax=6
imin=1
i=$imin
while [ $i -ge $imin -a $i -le $imax ]
do
    cp ../../../src/wallet/KintoWallet.sol ./KintoWallet_origin.sol
    file="$mutateFileA""$i""$mutateFileB"
    #echo $file
    cp $file ../../../src/wallet/KintoWallet.sol
    cd ../../../
    echo "KintoWallet mutation" "$i"
    certoraRun ./certora/mutations/KintoWallet/KintoWallet.conf --msg "KintoWallet mutation"" $i"
    echo "Mutation $i ran successfully"
    cd ./certora/mutations/KintoWallet
    mv ./KintoWallet_origin.sol ../../../src/wallet/KintoWallet.sol
    i=$(($i+1))
done