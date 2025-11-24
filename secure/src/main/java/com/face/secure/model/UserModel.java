package com.face.secure.model;

import java.util.Objects;



public class UserModel {
    private long id;
    private String name;
    private int label;

    public UserModel() {
    }

    public UserModel(long id, String name, int label) {
        this.id = id;
        this.name = name;
        this.label = label;
    }

    public int getLabel() {
        return label;
    }

    public void setLabel(int label) {
        this.label = label;
    }
    
    public long getId() {
        return id;
    }

    public void setId(long id) {
        this.id = id;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }
    
    @Override
    public String toString() {
        return "UserModel{" +
                "id=" + id +
                ", name='" + name + '\'' +
                ", label=" + label +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        UserModel userModel = (UserModel) o;
        return label == userModel.label && Objects.equals(id, userModel.id) && Objects.equals(name, userModel.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(id, name, label);
    }
}
