package com.face.secure.model;

import java.util.Objects;

public class UserModel {

    /*@ spec_public @*/
    private long id;

    /*@ spec_public non_null @*/
    private String name = "";

    /*@ spec_public @*/
    private int label;


    //@ public invariant name != null;

    public UserModel() {
    }

    /*@ requires name != null;
      @ ensures this.name == name; 
      @    
      */
    public UserModel(long id, String name, int label) {
        this.id = id;
        this.name = name;
        this.label = label;
    }
    
    /*@ pure @*/
    public int getLabel() {
        return label;
    }
    
    public void setLabel(int label) {
        this.label = label;
    }
    
    /*@ pure @*/
    public  long getId() {
        return id;
    }

    public void setId(long id) {
        this.id = id;
    }

    public /*@ pure non_null @*/ String getName() {
        return name;
    }

    /*@ requires name != null; @*/
    public void setName(String name) {
        this.name = name;
    }

    //@ skipesc    
    @Override
    public String toString() {
        return "UserModel{" +
                "id=" + id +
                ", name='" + name + '\'' +
                ", label=" + label +
                '}';
    }

    //@ skipesc
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        UserModel userModel = (UserModel) o;
        return label == userModel.label && Objects.equals(id, userModel.id) && Objects.equals(name, userModel.name);
    }

    //@ skipesc
    @Override
    public int hashCode() {
        return Objects.hash(id, name, label);
    }
}
