import React from 'react'
import Helmet from 'react-helmet'
import Link from 'gatsby-link'
import rehypeReact from "rehype-react";

import '../components/prism-lisp'
import AnnotatedCode from '../components/AnnotatedCode'
import Bios from '../components/Bio'
import "katex/dist/katex.min.css"

const renderAst = new rehypeReact({
  createElement: React.createElement,
  components: { "annotated-code": AnnotatedCode }
}).Compiler;

class BlogPostTemplate extends React.Component {
  render() {
    const {data,pathContext} = this.props;
    const post = data.markdownRemark;
    const {title: siteTitle, siteUrl} = data.site.siteMetadata;
    const { previous, next } = pathContext
    const { authors, title, date, description, image } = post.frontmatter;

    const imageUrl = image && `${siteUrl}${image}`;

    return (
      <div
        style={{
          marginBottom: 200,
        }}>
        <Helmet title={`${title} | ${siteTitle}`}>
          <meta property="og:type" content="article" />
          <meta property="og:title" content={title} />
          <meta property="og:description" content={description} />
          {imageUrl && (
            <meta property="og:image" content={imageUrl} />
          )}
          {imageUrl ? (
            <meta name="twitter:card" content="summary_large_image" />
          ) : (
            <meta name="twitter:card" content="summary" />
          )}
          <meta name="twitter:site" content="@monic_hq" />
        </Helmet>
        <h1>{title}</h1>
        <p
          style={{
            display: 'block',
            marginBottom: '50px',
          }}
        >
          {date}
        </p>
        {renderAst(post.htmlAst)}
        <hr
          style={{
            backgroundColor: '#0a2e6b',
            margin: '30px 0',
            height: '1px',
            border: 'none',
          }}
        />
        <Bios names={authors} />

        {/*
        <ul
          style={{
            display: 'flex',
            flexWrap: 'wrap',
            justifyContent: 'space-between',
            listStyle: 'none',
            padding: 0,
          }}
        >
          {previous && (
            <li>
              <Link to={previous.fields.slug} rel="prev">
                ← {previous.frontmatter.title}
              </Link>
            </li>
          )}

          {next && (
            <li>
              <Link to={next.fields.slug} rel="next">
                {next.frontmatter.title} →
              </Link>
            </li>
          )}
        </ul>
        */}
      </div>
    )
  }
}

export default BlogPostTemplate

export const pageQuery = graphql`
  query BlogPostBySlug($slug: String!) {
    site {
      siteMetadata {
        title
        siteUrl
      }
    }
    markdownRemark(fields: { slug: { eq: $slug } }) {
      id
      htmlAst
      frontmatter {
        title
        date(formatString: "MMMM DD, YYYY")
        authors
        description
        image
      }
    }
  }
`
