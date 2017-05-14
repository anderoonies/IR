#!/bin/bash

dirName="322_submission" ;
origDir=`pwd` ;

# Copy all files to an empty directory
if test -d ../$dirName ; then
  echo "ERROR: Please delete ../$dirName" ;
  exit 1 ;
fi
mkdir ../$dirName ;
cd ../$dirName ;
cp -r "${origDir}"/* ./ ;

# Remove unnecessary files
rm -r lib Makefile scripts bin ;
rm -r */tests ;
rm -fr */obj ;
rm -fr */bin ;
rm -r */scripts ;
rm  */Makefile ;
for i in `ls` ; do
  if ! test -d $i ; then
    continue ;
  fi
  pushd ./ ;
  cd $i ;
  for j in `ls` ; do
    if test -d $j ; then
      continue ;
    fi
    rm -f $j ;
  done
  popd ;
done

# Create the package
cd ../ ;
rm -f ${dirName}.tar.bz2 ;
tar cfj ${dirName}.tar.bz2 ${dirName} ;
mv ${dirName}.tar.bz2 "${origDir}"/ ;
rm -r ${dirName} ;
