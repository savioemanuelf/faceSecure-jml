package com.face.secure.service;

import com.face.secure.model.UserModel;
import com.face.secure.repositories.UserRepository;

public class UserService {
    private /*@ spec_public @*/ final UserRepository userRepository;

    //@ public invariant userRepository != null;

    /*@ requires userRepository != null;
      @ ensures this.userRepository == userRepository;
      @*/
    public UserService(UserRepository userRepository) {
        this.userRepository = userRepository;
    }

    /*@ requires user != null;
      @ ensures \result == user;
      @*/
    public UserModel create(UserModel user) {
        if (user == null) {
            throw new IllegalArgumentException("User cannot be null");
        }
        return userRepository.save(user);
    }

    /*@ requires label >= 0;
      @ ensures \result != null;
      @*/
    public /*@ pure @*/ String getNameByLabel(int label) {
        /*@ nullable @*/ UserModel user = userRepository.findByLabel(label);
        
        if (user != null) {
            return user.getName();
        }
        return "Unknown";
    }
}