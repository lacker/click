#!/usr/bin/env click
(:match
  (:handlers
    (:left (:lambda (:param :x :body (:var :x)))
     :right (:lambda (:param :y :body :wrong)))
   :value
    (:left :payload)))
