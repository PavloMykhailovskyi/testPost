import React from "react";
import { useState, useEffect,useContext } from "react";
import axios from "axios";
import { CircularProgress } from "@mui/material";
import PostList from "./PostList";
import { BlogContext } from "../context/blog-context";

export const PostGrid = ({authorId,to}) => {
  const ctx=useContext(BlogContext)
  console.log(ctx)
  const [authorPosts, setAuthorPosts] = useState({
    status: "loading",
    posts: [],
  });
  useEffect(() => {
    
    async function makeRequest(){
    try {
      console.log("abhi")
      const res = await axios.get(`http://localhost:5000/api/posts/author/${authorId}`,{headers:{ "Authorization": `${ctx.key} ${ctx.id}`}});
      console.log("tabhi")

      setAuthorPosts({ status: "done", posts: res.data.posts });
    } catch (error) {
      setAuthorPosts({ status: "error", error: error.message });
      console.error(error);
    }
  };
  makeRequest();
  }, [authorId]);

  if (authorPosts.status === "loading") {
    return  <center><CircularProgress/></center>;
  }

  if (authorPosts.status === "error") {
    return <div>{authorPosts.message}</div>;
  }

  return (
    <div>
      <br/>
      <PostList key={authorId} to={to} posts={authorPosts.posts} />
    </div>
  );
};

;
