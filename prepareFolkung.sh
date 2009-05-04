#!/bin/bash

if [ ! -d $1 ] ; 
then
	tar xvzf $2
	patch $1/Haskell/Form.hs folkung-warnings.patch
fi